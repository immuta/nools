"use strict";
var it = require("it"),
    assert = require("assert"),
    nools = require("../index"),
    GraphNode = require("../lib/nodes/node");

it.describe("issues", function (it) {

    // Node.dispose visited map: cycles and diamonds must not blow the stack.
    it.describe("dispose shared graph", function (it) {

        // Smoke: 2-node cycle must terminate (stack overflow = bug).
        it.should("not recurse infinitely when dispose encounters a directed cycle through shared nodes", function () {
            var a = new GraphNode(),
                b = new GraphNode(),
                pattern = {}
            ;
            a.addOutNode(b, pattern);
            b.addOutNode(a, pattern);
            assert.doesNotThrow(function () {
                a.dispose();
            });
        });

        // External visited map: each node exactly once in a large ring.
        it.should("visit each node in a large directed cycle once (visited map matches graph size)", function () {
            var n = 250,
                nodes = [],
                pattern = {},
                i
            ;
            for (i = 0; i < n; i++) {
                nodes.push(new GraphNode());
            }
            for (i = 0; i < n; i++) {
                nodes[i].addOutNode(nodes[(i + 1) % n], pattern);
            }
            var visited = {};
            nodes[0].dispose(undefined, visited);
            assert.equal(Object.keys(visited).length, n);
            for (i = 0; i < n; i++) {
                assert.isTrue(visited[nodes[i].__count], "node index " + i + " __count " + nodes[i].__count);
            }
        });

        // Wrapper counts entries: ring closure causes one extra call that hits visited[] and returns.
        it.should("short-circuit when dispose re-enters a node (visited prevents unbounded recursion)", function () {
            var n = 100,
                nodes = [],
                pattern = {},
                i,
                originalDispose = GraphNode.prototype.dispose,
                entries = {}
            ;
            GraphNode.prototype.dispose = function (assertable, visited) {
                var c = this.__count;
                entries[c] = (entries[c] || 0) + 1;
                return originalDispose.call(this, assertable, visited);
            };
            try {
                for (i = 0; i < n; i++) {
                    nodes.push(new GraphNode());
                }
                for (i = 0; i < n; i++) {
                    nodes[i].addOutNode(nodes[(i + 1) % n], pattern);
                }
                nodes[0].dispose();
                var totalCalls = Object.keys(entries).reduce(function (acc, k) {
                    return acc + entries[k];
                }, 0);
                assert.equal(totalCalls, n + 1, "one extra dispose entry when the cycle closes; without visited this never finishes");
                assert.equal(entries[nodes[0].__count], 2, "start node is entered again and must return immediately");
                for (i = 1; i < n; i++) {
                    assert.equal(entries[nodes[i].__count], 1);
                }
            } finally {
                GraphNode.prototype.dispose = originalDispose;
            }
        });

        // RootNode-style: two type trees, one visited object; self-edge on shared node.
        it.should("mark every reachable node when two roots share one visited map (like RootNode.dispose)", function () {
            var pattern = {},
                a = new GraphNode(),
                b = new GraphNode(),
                shared = new GraphNode()
            ;
            a.addOutNode(shared, pattern);
            b.addOutNode(shared, pattern);
            shared.addOutNode(shared, pattern);
            var visited = {};
            a.dispose(undefined, visited);
            b.dispose(undefined, visited);
            assert.equal(Object.keys(visited).length, 3);
            assert.isTrue(visited[a.__count]);
            assert.isTrue(visited[b.__count]);
            assert.isTrue(visited[shared.__count]);
        });

    });

    it.describe("62", function (it) {
        it.should("allow rule names with \" character in constraints", function () {
            assert.isTrue(/"s == \\"hello\\""/.test(nools.transpile('rule "issue62" {when {s : String s == "hello";}then {emit("s", s);}}', {name: "issue62"})));
        });
    });

    it.describe("65", function (it) {

        function Thing(step) {
            this.step = step;
        }

        Thing.prototype.world = "world";

        Thing.prototype.hello = function () {
            return "hello";
        };

        var flow;
        it.beforeAll(function () {
            flow = nools.flow("issue65", function () {

                this.rule("issue65",
                    [Thing, "$t", "($t.step && isUndefined($t[$t.step]))"],
                    function (facts, flow) {
                        flow.emit("thing", facts.$t);
                    });
            });
        });

        it.should("allow property lookup using [] instead of . notation", function () {
            var calledWith = [];
            return flow.getSession(new Thing("hello"), new Thing("world"), new Thing("other"), new Thing("other2"))
                .on("thing", function (t) {
                    calledWith.push(t);
                })
                .match().then(function () {
                    assert.lengthOf(calledWith, 2);
                    assert.equal(calledWith[0].step, "other2");
                    assert.equal(calledWith[1].step, "other");
                });
        });

    });

    it.describe("66", function (it) {


        var flow, Value;
        it.beforeAll(function () {
            flow = nools.compile(
                    "define Value {id : null,v : null,constructor : function (id, value) {this.id = id;this.v = value;} }" +
                    "rule 'issue66' {when {v4 : Value v4.id =~ /xyz/ && v4.v == 27;}then {emit('v4', v4);}}", {name: "issue66"});
            Value = flow.getDefined("value");
        });

        it.should("properly evaluate a rule with a regular expressions and equality", function () {
            var called = 0;
            return flow.getSession(new Value("xyz", 27), new Value("xyz", 27))
                .on("v4", function () {
                    called++;
                })
                .match().then(function () {
                    assert.equal(called, 2);
                });
        });
    });

    it.describe("67", function (it) {
        var flow, Value;
        it.beforeAll(function () {
            flow = nools.compile(
                    "define Value {id : null,v : null,constructor : function (id, value) {this.id = id;this.v = value;} }" +
                    "rule 'issue67' {when {v4 : Value v4.id =~ /xyz/ && v4.v =~ /abc/;}then {emit('v4', v4);}}", {name: "issue67"});
            Value = flow.getDefined("value");
        });

        it.should("properly evaluate a rule with multiple regular expressions", function () {
            var called = 0;
            return flow.getSession(new Value("xyz", "abc"), new Value("xyz", "abc"))
                .on("v4", function () {
                    called++;
                })
                .match().then(function () {
                    assert.equal(called, 2);
                });
        });
    });

    it.describe("69", function (it) {
        it.should("allow rule names with unescaped ' values", function () {
            assert.isTrue(/'69\\'s issue'/.test(nools.transpile("rule \"69's issue\" {when {s : String s == 'hello';}then {emit('s', s);}}", {name: "issue69"})));

        });
    });

    it.describe("81", function (it) {

        it.should("allow array references when compiling rules", function () {

            function ActualWeightDomain(values) {
                this.values = values;
            }

            function ActualWeightEnteredValue(value) {
                this.value = value;
            }

            function ActualWeightValue() {

            }

            var src = "rule CheckAndAssertActualWeight {" +
                " when {" +
                "    actualWeight_domain: ActualWeightDomain {values: _domainValues};" +
                "    actualWeight_EnteredValue: ActualWeightEnteredValue" +
                "    (" +
                "        actualWeight_EnteredValue.value >= _domainValues[0] &&" +
                "            actualWeight_EnteredValue.value <= _domainValues[1]" +
                "    ) {value : _entered};" +
                "}" +
                "then {" +
                "    assert( new ActualWeightValue({value:_entered}) );" +
                "}" +
                "}";

            var flow = nools.compile(src, {name: "issue81", define: {
                "ActualWeightDomain": ActualWeightDomain,
                "ActualWeightEnteredValue": ActualWeightEnteredValue,
                ActualWeightValue: ActualWeightValue
            }});
            var fired = [];
            var session = flow.getSession(new ActualWeightEnteredValue(1), new ActualWeightDomain([1, 2])).on("fire", function (name) {
                fired.push(name);
            });
            return session.match().then(function () {
                assert.deepEqual(fired, ["CheckAndAssertActualWeight"]);
                fired.length = 0;
                session = flow.getSession(new ActualWeightEnteredValue(5), new ActualWeightDomain([1, 2])).on("fire", function (name) {
                    fired.push(name);
                });
                return session.match().then(function () {
                    assert.deepEqual(fired, []);
                });
            });

        });

    });

    it.describe("82", function (it) {

        it.should("allow a trailing comment when using the dsl", function () {
            nools.compile("rule 'hello' {when {s: String s == 'hello';}then{console.log(s);}} //test comment ", {name: "issue82"});
        });

    });

    it.describe("85", function (it) {

        it.should("allow multiple not clauses in an or condition", function () {

            var flowSrc = " rule MultiNotOrRule {" +
                "   when {" +
                "       or (" +
                "           not(n1: Number n1 == 1)," +
                "           not(s1: String s1 == 'hello')," +
                "           not(d1: Date d1.getDate() == now().getDate())" +
                "       )" +
                "   }" +
                "   then{" +
                "       emit('called', n1, s1, d1)" +
                "   }" +
                "}";
            var flow = nools.compile(flowSrc, {name: "issue85"});
            var called = 0;
            return flow.getSession()
                .on("called", function () {
                    called++;
                }).match()
                .then(function () {
                    assert.equal(called, 3);
                    called = 0;
                    return flow.getSession(1).on("called", function () {
                        called++;
                    }).match();
                })
                .then(function () {
                    assert.equal(called, 2);
                    called = 0;
                    return flow.getSession('hello').on("called", function () {
                        called++;
                    }).match();
                })
                .then(function () {
                    assert.equal(called, 2);
                    called = 0;
                    return flow.getSession(new Date()).on("called", function () {
                        called++;
                    }).match();
                })
                .then(function () {
                    assert.equal(called, 2);
                    called = 0;
                    return flow.getSession(1, 'hello', new Date()).on("called", function () {
                        called++;
                    }).match();
                })
                .then(function () {
                    assert.equal(called, 0);
                    return flow.getSession(1, 'hello', new Date()).on("called", function () {
                        called++;
                    }).match();
                });
        });
    });

    it.describe("89", function (it) {

        var flow;

        function Person(address) {
            this.address = address;
        }

        it.beforeAll(function () {
            flow = nools.flow("issue 89", function () {

                this.rule("from with missing property", [
                    [Person, "p"],
                    [Number, "zipcode", "from p.address.zipcode"]
                ], function () {

                });
            });
        });

        it.should("not throw an error on missing properties", function () {
            return flow.getSession(new Person({})).match();
        });

        it.should("should throw an error if the from references a property on a value that is undefined", function () {
            try {
                flow.getSession(new Person()).match();
                assert.fail();
            } catch (e) {
                assert.ok(true);
            }
        });
    });

    it.describe("109", function (it) {
        var flow;


        it.beforeAll(function () {
            flow = nools.compile("rule 'issue109' {when {exists(s1 : String);}then {emit('exists');}}", {name: "issue109"});
        });

        it.should("properly evaluate a rule with an exists constraint", function () {
            var called = 0;
            return flow.getSession("Hello")
                .on("exists", function () {
                    called++;
                })
                .match().then(function () {
                    assert.equal(called, 1);
                });
        });
    });


    it.describe("122", function (it) {
        var flow;
        it.beforeAll(function () {
            flow = nools.compile("define Point {x: 0, y: 0, constructor: function(x, y) {this.x = x; this.y = y; } } define Line {points: null, constructor : function() {this.points = []; }, addPoint: function(x, y) {this.points.push(new Point(x,y)); } }", {name: "issue122"});
        });

        it.should("be able to access defined classes within another classes scope", function () {
            var Line = flow.getDefined("Line");
            var myLine = new Line();
            myLine.addPoint(5, 5);
        });
    });

    it.describe("127", function (it) {
        var flow, callbackCalled;
        it.beforeAll(function () {
            flow = nools.compile("", {name: "issue127"}, function() {
                callbackCalled = true;
            });
        });

        it.should("callback should be called even if config provided", function () {
            assert.truthy(callbackCalled);
        });
    });
});