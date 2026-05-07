"use strict";
// Regression suite for session.dispose: beta memories, Not/From maps, agenda, working memory.
var it = require("it"),
    assert = require("assert"),
    declare = require("declare.js"),
    nools = require("../index"),
    Memory = require("../lib/nodes/misc/memory");

/** DFS from type nodes; picks up beta-like nodes (Not/From are not only in root.joinNodes). */
function collectBetaLikeNodes(root) {
    var seen = {};
    var out = [];

    function visit(n) {
        if (!n || seen[n.__count]) {
            return;
        }
        seen[n.__count] = true;
        if (n.leftTuples && n.rightTuples) {
            out.push(n);
        }
        var es = n.__entrySet, i;
        if (es) {
            for (i = es.length - 1; i >= 0; i--) {
                visit(es[i].key);
            }
        }
    }

    var tns = root.typeNodes, j;
    for (j = tns.length - 1; j >= 0; j--) {
        visit(tns[j]);
    }
    return out;
}

/** Assert join hashes, tuple stores, and optional Not/From side maps. */
function assertBetaStoresEmpty(n) {
    assert.equal(Object.keys(n.leftMemory).length, 0, "leftMemory keys for " + (n.nodeType || n.toString()));
    assert.equal(Object.keys(n.rightMemory).length, 0, "rightMemory keys");
    assert.equal(n.leftTuples.length, 0, "leftTuples.length");
    assert.equal(n.rightTuples.length, 0, "rightTuples.length");
    if (n.leftTupleMemory) {
        assert.equal(Object.keys(n.leftTupleMemory).length, 0, "leftTupleMemory");
    }
    if (n.fromMemory) {
        assert.equal(Object.keys(n.fromMemory).length, 0, "fromMemory");
    }
}

/** Facts list + agenda rules cleared (public session surface). */
function assertSessionStoresDisposed(session) {
    assert.strictEqual(session.workingMemory.facts.head, null, "workingMemory facts list head");
    assert.strictEqual(session.workingMemory.facts.tail, null);
    assert.strictEqual(session.workingMemory.facts.length, 0);
    assert.deepEqual(session.getFacts(), []);
    assert.deepEqual(session.agenda.rules, {}, "agenda.rules");
}

/** Wrap session.dispose; count Memory#clear / clearIndexes (left+right per beta). */
function disposeWithMemorySpies(session) {
    var originalClear = Memory.prototype.clear;
    var originalClearIndexes = Memory.prototype.clearIndexes;
    var clearCount = 0;
    var clearIndexesCount = 0;
    Memory.prototype.clear = function () {
        clearCount++;
        return originalClear.apply(this, arguments);
    };
    Memory.prototype.clearIndexes = function () {
        clearIndexesCount++;
        return originalClearIndexes.apply(this, arguments);
    };
    try {
        session.dispose();
    } finally {
        Memory.prototype.clear = originalClear;
        Memory.prototype.clearIndexes = originalClearIndexes;
    }
    return { clearCount: clearCount, clearIndexesCount: clearIndexesCount };
}

/** Flow names registered in this file (deleteFlow in afterAll). */
var FLOW_NAMES = [
    "disposeMemJoin",
    "disposeMemChain",
    "disposeMemNot",
    "disposeMemPlainBeta",
    "disposeMemRefJoin",
    "disposeMemTwoRules",
    "disposeMemFrom",
    "disposeMemExists",
    "disposeMemExistsFrom",
    "disposeMemFromNot",
    "disposeMemOr",
    "disposeCompileMem",
    "disposeMemNoMatch",
    "disposeMemIdempotent",
    "disposeMemAgenda"
];

it.describe("session.dispose clears beta memory", function (it) {

    // Compiled + flow() names; must delete or second test run throws “already defined”.
    it.afterAll(function () {
        var i = FLOW_NAMES.length;
        while (--i >= 0) {
            nools.deleteFlow(FLOW_NAMES[i]);
        }
    });

    // Simple join, chains, Not, Beta vs Join, multi-rule.
    it.describe("core join networks", function (it) {

        // Proves left/right Memory.clear per beta and WM + agenda flush.
        it.should("invoke Memory#clear / clearIndexes twice per beta-like node (simple join)", function () {
            var flow = nools.flow("disposeMemJoin", function () {
                this.rule("r", [[String, "a"], [Number, "n"]], function () {});
            });
            var session = flow.getSession("x", 1);
            return session.match().then(function () {
                var betas = collectBetaLikeNodes(session.rootNode);
                assert.ok(betas.length >= 1, "expected at least one join node");

                var spies = disposeWithMemorySpies(session);

                assert.equal(spies.clearCount, betas.length * 2);
                assert.equal(spies.clearIndexesCount, spies.clearCount, "clear() always calls clearIndexes()");
                var i = betas.length;
                while (--i >= 0) {
                    assertBetaStoresEmpty(betas[i]);
                }
                assertSessionStoresDisposed(session);
            });
        });

        // Chained joins: first beta must propagate dispose to downstream betas.
        it.should("clear every beta-like node in a multi-join rule", function () {
            var flow = nools.flow("disposeMemChain", function () {
                this.rule("r", [
                    [String, "a"],
                    [String, "b"],
                    [Number, "n"]
                ], function () {});
            });
            var session = flow.getSession("x", "y", 7);
            return session.match().then(function () {
                var betas = collectBetaLikeNodes(session.rootNode);
                assert.ok(betas.length >= 2, "chained patterns should create multiple joins");

                var spies = disposeWithMemorySpies(session);

                assert.equal(spies.clearCount, betas.length * 2);
                var i = betas.length;
                while (--i >= 0) {
                    assertBetaStoresEmpty(betas[i]);
                }
            });
        });

        // NotNode.leftTupleMemory is extra state on top of BetaNode disposal.
        it.should("clear NotNode auxiliary maps and tuple stores", function () {
            var flow = nools.flow("disposeMemNot", function () {
                this.rule("order", [
                    [Number, "n1"],
                    ["not", Number, "n2", "n1 != n2 && n1 > n2"]
                ], function () {});
            });
            var session = flow.getSession(3, 1, 5, 2, 4);
            return session.match().then(function () {
                var betas = collectBetaLikeNodes(session.rootNode);
                assert.ok(betas.length >= 1);
                var hasNot = false;
                var i = betas.length;
                while (--i >= 0) {
                    if (betas[i].nodeType === "NotNode") {
                        hasNot = true;
                    }
                }
                assert.isTrue(hasNot, "fixture should include a NotNode");

                session.dispose();

                i = betas.length;
                while (--i >= 0) {
                    assertBetaStoresEmpty(betas[i]);
                }
            });
        });

        // No ReferenceConstraint on either pattern side => plain BetaNode (not JoinNode).
        it.should("clear plain BetaNode networks (no reference constraints on either side)", function () {
            var flow = nools.flow("disposeMemPlainBeta", function () {
                this.rule("r", [
                    [String, "a", "a == 'hi'"],
                    [String, "b", "b == 'there'"]
                ], function () {});
            });
            var session = flow.getSession("hi", "there");
            return session.match().then(function () {
                var betas = collectBetaLikeNodes(session.rootNode);
                assert.ok(betas.some(function (b) {
                    return b.nodeType === "BetaNode";
                }), "expected a plain BetaNode join");
                session.dispose();
                var i = betas.length;
                while (--i >= 0) {
                    assertBetaStoresEmpty(betas[i]);
                }
            });
        });

        // Cross-pattern reference => JoinNode; memories must still empty after dispose.
        it.should("clear JoinNode networks with cross-pattern references", function () {
            var flow = nools.flow("disposeMemRefJoin", function () {
                this.rule("r", [
                    [String, "s1"],
                    [String, "s2", "s2 == s1"]
                ], function () {});
            });
            var session = flow.getSession("same", "same");
            return session.match().then(function () {
                var betas = collectBetaLikeNodes(session.rootNode);
                assert.ok(betas.some(function (b) {
                    return b.nodeType === "JoinNode";
                }), "reference constraints should use JoinNode");
                session.dispose();
                var i = betas.length;
                while (--i >= 0) {
                    assertBetaStoresEmpty(betas[i]);
                }
            });
        });

        // Two rules => two alpha subgraphs; every beta in the session graph clears.
        it.should("clear all join nodes when the flow defines multiple rules", function () {
            var flow = nools.flow("disposeMemTwoRules", function () {
                this.rule("a", [[String, "x"], [Number, "n"]], function () {});
                this.rule("b", [[String, "y"], [Boolean, "b"]], function () {});
            });
            var session = flow.getSession("p", 1, "q", true);
            return session.match().then(function () {
                var betas = collectBetaLikeNodes(session.rootNode);
                assert.ok(betas.length >= 2, "two rules should contribute disjoint join subgraphs");
                var spies = disposeWithMemorySpies(session);
                assert.equal(spies.clearCount, betas.length * 2);
                var i = betas.length;
                while (--i >= 0) {
                    assertBetaStoresEmpty(betas[i]);
                }
            });
        });
    });

    // FromNode, exists variants, from+not, or-replicated rules, compile() path.
    it.describe("from / exists / or / compiled flows", function (it) {

        var Address = declare({
            instance: {
                constructor: function (zip) {
                    this.zipcode = zip;
                }
            }
        });
        var Person = declare({
            instance: {
                constructor: function (first, last, address) {
                    this.firstName = first;
                    this.lastName = last;
                    this.address = address;
                }
            }
        });

        // fromMemory fills during match; FromNode.dispose must drop it before super.
        it.should("clear FromNode fromMemory and tuple stores", function () {
            var flow = nools.flow("disposeMemFrom", function () {
                this.rule("fromdispose", [
                    [Person, "p"],
                    [Address, "a", "a.zipcode == 88847", "from p.address"]
                ], function () {});
            });
            var session = flow.getSession(new Person("bob", "yukon", new Address(88847)));
            return session.match().then(function () {
                var betas = collectBetaLikeNodes(session.rootNode);
                var hasFrom = false;
                var i = betas.length;
                while (--i >= 0) {
                    if (betas[i].nodeType === "FromNode") {
                        hasFrom = true;
                    }
                }
                assert.isTrue(hasFrom, "fixture should include FromNode");
                var fromNodes = betas.filter(function (b) {
                    return b.nodeType === "FromNode";
                });
                assert.ok(Object.keys(fromNodes[0].fromMemory).length > 0, "fromMemory populated before dispose");
                session.dispose();
                i = betas.length;
                while (--i >= 0) {
                    assertBetaStoresEmpty(betas[i]);
                }
            });
        });

        // ExistsNode subclasses NotNode (blocking / leftTupleMemory paths).
        it.should("clear ExistsNode (extends NotNode) tuple and blocking maps", function () {
            var C = function () {
                this.n = 0;
            };
            var flow = nools.flow("disposeMemExists", function () {
                this.rule("ex", [
                    ["exists", String, "s"],
                    [C, "c"]
                ], function () {});
            });
            var session = flow.getSession(new C(), "a", "b");
            return session.match().then(function () {
                var betas = collectBetaLikeNodes(session.rootNode);
                assert.ok(betas.some(function (b) {
                    return b.nodeType === "ExistsNode";
                }));
                session.dispose();
                var i = betas.length;
                while (--i >= 0) {
                    assertBetaStoresEmpty(betas[i]);
                }
            });
        });

        // Exists + from uses ExistsFromNode; inherits fromMemory cleanup from FromNot path.
        it.should("clear ExistsFromNode fromMemory", function () {
            function PersonZip(z) {
                this.zipcodes = z;
            }
            var C = function () {
                this.n = 0;
            };
            var flow = nools.flow("disposeMemExistsFrom", function () {
                this.rule("exf", [
                    [PersonZip, "p"],
                    ["exists", Number, "zip", "zip == 11111", "from p.zipcodes"],
                    [C, "c"]
                ], function () {});
            });
            var session = flow.getSession(new C(), new PersonZip([33333, 22222, 11111]));
            return session.match().then(function () {
                var betas = collectBetaLikeNodes(session.rootNode);
                assert.ok(betas.some(function (b) {
                    return b.nodeType === "ExistsFromNode";
                }));
                session.dispose();
                var i = betas.length;
                while (--i >= 0) {
                    assertBetaStoresEmpty(betas[i]);
                }
            });
        });

        // not + from collection: FromNotNode keeps fromMemory for generated facts.
        it.should("clear FromNotNode (not … from …) fromMemory", function () {
            var FriendPerson = declare({
                instance: {
                    constructor: function (first, last, friends) {
                        this.firstName = first;
                        this.lastName = last;
                        this.friends = friends || [];
                    }
                }
            });
            var flow = nools.flow("disposeMemFromNot", function () {
                this.rule("fn", [
                    [FriendPerson, "p"],
                    ["not", FriendPerson, "friend", "p !== friend && friend.lastName !== p.lastName", "from p.friends"]
                ], function () {});
            });
            var a = new FriendPerson("a", "yuk", []);
            var b = new FriendPerson("b", "yuko", []);
            a.friends.push(b);
            var session = flow.getSession(a, b);
            return session.match().then(function () {
                var betas = collectBetaLikeNodes(session.rootNode);
                assert.ok(betas.some(function (bn) {
                    return bn.nodeType === "FromNotNode";
                }));
                session.dispose();
                var i = betas.length;
                while (--i >= 0) {
                    assertBetaStoresEmpty(betas[i]);
                }
            });
        });

        // or() clones into multiple rules; session root still owns one combined network walk.
        it.should("clear networks produced by or patterns (multiple rule replicas)", function () {
            var Cntr = function () {
                this.k = 0;
            };
            var flow = nools.flow("disposeMemOr", function () {
                this.rule("orr", [
                    ["or",
                        [String, "s", "s == 'hello'"],
                        [String, "s", "s == 'world'"]
                    ],
                    [Cntr, "c"]
                ], function () {});
            });
            var session = flow.getSession("world", new Cntr());
            return session.match().then(function () {
                var betas = collectBetaLikeNodes(session.rootNode);
                assert.ok(betas.length >= 1);
                session.dispose();
                var i = betas.length;
                while (--i >= 0) {
                    assertBetaStoresEmpty(betas[i]);
                }
            });
        });

        // compile() flow + getSession: same dispose contract as nools.flow().
        it.should("dispose compiled DSL flow and clear beta memory", function () {
            var flow = nools.compile(
                "rule disposeDsl { when { a: String; b: Number; } then { } }",
                { name: "disposeCompileMem" }
            );
            var session = flow.getSession("z", 9);
            return session.match().then(function () {
                var betas = collectBetaLikeNodes(session.rootNode);
                assert.ok(betas.length >= 1);
                var spies = disposeWithMemorySpies(session);
                assert.equal(spies.clearCount, betas.length * 2);
                assertSessionStoresDisposed(session);
            });
        });
    });

    // Activations and per-rule trees dropped while beta dispose runs separately.
    it.describe("agenda", function (it) {

        // Fired rule leaves agenda.rules populated; dispose must zero activations.
        it.should("remove all activations and per-rule agenda bookkeeping", function () {
            var fired = false;
            var flow = nools.flow("disposeMemAgenda", function () {
                this.rule("fires", [[String, "a"]], function () {
                    fired = true;
                });
            });
            var session = flow.getSession("x");
            return session.match().then(function () {
                assert.isTrue(fired);
                assert.ok(Object.keys(session.agenda.rules).length > 0, "rules registered activations");
                session.dispose();
                assert.deepEqual(session.agenda.rules, {});
                assert.isTrue(session.agenda.isEmpty());
            });
        });
    });

    // No match path, double dispose.
    it.describe("edge cases and invariants", function (it) {

        // No match run: still safe to dispose (InitialFact cleared with WM).
        it.should("dispose a session that never ran match()", function () {
            var flow = nools.flow("disposeMemNoMatch", function () {
                this.rule("r", [[String, "a"]], function () {});
            });
            var session = flow.getSession("only");
            var betas = collectBetaLikeNodes(session.rootNode);
            assert.doesNotThrow(function () {
                session.dispose();
            });
            var i = betas.length;
            while (--i >= 0) {
                assertBetaStoresEmpty(betas[i]);
            }
            assertSessionStoresDisposed(session);
        });

        // Defensive: callers may invoke dispose more than once.
        it.should("allow dispose() twice without throwing (idempotent)", function () {
            var flow = nools.flow("disposeMemIdempotent", function () {
                this.rule("r", [[String, "a"], [Number, "n"]], function () {});
            });
            var session = flow.getSession("q", 3);
            return session.match().then(function () {
                var betas = collectBetaLikeNodes(session.rootNode);
                session.dispose();
                assert.doesNotThrow(function () {
                    session.dispose();
                });
                var i = betas.length;
                while (--i >= 0) {
                    assertBetaStoresEmpty(betas[i]);
                }
                assertSessionStoresDisposed(session);
            });
        });
    });
});
