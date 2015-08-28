import string-dict as D
import equality as E
import valueskeleton as VS
import "atom.arr" as A
import "term.arr" as T
import "sugar.arr" as S

type Var = A.Var
mk-var = A.mk-var
free-var = A.free-var
var-to-str = A.var-to-str

type Term = T.Term
signature = T.signature
s-empty = T.s-empty
s-child = T.s-child
s-union = T.s-union
s-compose = T.s-compose
t-node = T.t-node
t-refn = T.t-refn
t-decl = T.t-decl
t-hole = T.t-hole
t-tag = T.t-tag
t-val = T.t-val
is-t-node = T.is-t-node
resolve = T.resolve
unresolve = T.unresolve
iso = T.iso

_match = S._match
substitute = S.substitute
desugar = S.desugar-full
resugar = S.resugar-full

data Config:
  | config(term :: Term, env :: D.StringDict)
  | answer(val :: Any)
end


# From the paper
check "Port Test":
  sigs = [D.string-dict:
    "plus", signature([list: s-empty, s-empty], s-empty),
    "if", signature([list: s-empty, s-empty, s-empty], s-empty),
    "let", signature([list: s-empty, s-empty, s-child(0)], s-empty),
    "write", signature([list: s-empty, s-empty], s-empty),
    "log", signature([list: s-empty, s-empty, s-empty], s-empty),
    "str", signature([list: s-empty], s-empty)
  ]

  fun step(term :: Term, env :: D.StringDict) -> Config:
    fun similar(x, y):
      # Tags are associated with a node
      (is-t-node(x) and is-t-node(y)) and (x.id == y.id)
    end
    cases(Term) term:
      | t-val(val) => answer(val)
      | t-tag(left, right, shadow term) =>
        cases(Config) step(term, env):
          | answer(val) => answer(val)
          | config(term2, env2) =>
            if similar(term, term2):
              config(t-tag(left, right, term2), env2)
            else:
              config(term2, env2)
            end
        end
      | t-refn(v) =>
        config(t-val(env.get-value(var-to-str(v))), env)
      | t-node(con, id, ts) =>
        ask:
          | con == "str" then:
            answer(ts.get(0).val)
          | con == "plus" then:
            cases(Config) step(ts.get(0), env):
              | answer(left) =>
                cases(Config) step(ts.get(1), env):
                  | answer(right) => answer(left + right)
                  | config(right, _) =>
                    config(t-node(con, id, [list: t-val(left), right]), env)
                end
              | config(left, _) =>
                config(t-node(con, id, [list: left, ts.get(1)]), env)
            end
          | con == "if" then:
            cases(Config) step(ts.get(0), env):
              | answer(cond) =>
                ask:
                  | cond == "true" then: config(ts.get(1), env)
                  | otherwise:           config(ts.get(2), env)
                end
              | config(cond, _) =>
                config(t-node(con, id, [list: cond, ts.get(1), ts.get(2)]), env)
            end
          | con == "let" then:
            cases(Config) step(ts.get(1), env):
              | answer(arg) =>
                new-env = env.set(var-to-str(ts.get(0).v), arg)
                config(ts.get(2), new-env)
              | config(arg, _) =>
                config(t-node(con, id, [list: ts.get(0), arg, ts.get(2)]), env)
            end
          | con == "write" then:
            # Not bothering to model side-effects
            cases(Config) step(ts.get(0), env):
              | answer(arg0) =>
                cases(Config) step(ts.get(1), env):
                  | answer(arg1) =>
                    answer("WRITE: " + arg0 + " TO: " + arg1)
                  | config(arg1, _) =>
                    config(t-node(con, id, [list: t-val(arg0), arg1]), env)
                end
              | config(arg0, _) =>
                config(t-node(con, id, [list: arg0, ts.get(1)]), env)
            end
        end
    end
  end

  fun str-node(str):
    t-node("str", 0, [list: t-val(str)])
  end
  fun if-node(a, b, c):
    t-node("if", 0, [list: a, b, c])
  end
  fun write-node(a, b):
    t-node("write", 0, [list: a, b])
  end
  fun let-node(a, b, c):
    t-node("let", 0, [list: t-decl(a), b, c])
  end
  fun plus-node(a, b):
    t-node("plus", 0, [list: a, b])
  end
  fun log-node(a, b, c):
    t-node("log", 0, [list: a, b, c])
  end

  fun test-step(term, expected):
    cases(Config) step(term, [D.string-dict:]):
      | answer(ans) => t-val(ans).display()
      | config(shadow term, _) => term.display()
    end is expected
  end

  test-step(str-node("ok"), "<ok>")
  test-step(plus-node(str-node("x"), str-node("y")), "<xy>")
  test-step(write-node(str-node("x"), str-node("y")),
    "<WRITE: x TO: y>")
  test-step(if-node(str-node("true"), str-node("then"), str-node("else")),
    "str(<then>)")
  test-step(if-node(str-node("false"), str-node("then"), str-node("else")),
    "str(<else>)")
  test-step(let-node(free-var("x"), str-node("a"), str-node("b")),
    "str(<b>)")
    
  fun desugar-log(ctx):
    let-node(free-var("port"),
      if-node(ctx.get(2), ctx.get(1), str-node("DEVNULL")),
      write-node(ctx.get(0), t-refn(free-var("port"))))
  end

  sugar = [D.string-dict:
    "log", desugar-log,
    "plus",  lam(ctx): ctx end,
    "if",    lam(ctx): ctx end,
    "write", lam(ctx): ctx end,
    "let",   lam(ctx): ctx end,
    "str",   lam(ctx): ctx end]

  port = free-var("port")
  verbose = free-var("verbose")
  test-term = let-node(port, str-node("80"),
    log-node(plus-node(str-node("Port: "), t-refn(port)),
      if-node(t-refn(verbose), str-node("stderr"), str-node("devnull")),
      str-node("true")))

  var STEPS = [list: test-term.display()]
  shadow test-term = desugar(sigs, sugar, test-term)

  fun eval(term :: Term):
    fun run(shadow term, env):
      cases(Config) step(term, env):
        | answer(val) => STEPS := link(t-val(val).display(), STEPS)
        | config(shadow term, shadow env) =>
          cases(Option) resugar(sigs, sugar, term):
            | none => nothing
            | some(shadow term) =>
              STEPS := link(term.display(), STEPS)
          end
          run(term, env)
      end
    end
    run(term, [D.string-dict: "verbose:0", "true"])
    STEPS := STEPS.reverse()
  end

  eval(test-term)

  STEPS.get(0) is "let($port, str(<80>), log(plus(str(<Port: >), port), if(verbose, str(<stderr>), str(<devnull>)), str(<true>)))"
  STEPS.get(1) is "log(plus(str(<Port: >), port), if(verbose, str(<stderr>), str(<devnull>)), str(<true>))"
  STEPS.get(2) is "<WRITE: Port: 80 TO: stderr>"
  
  nothing
end
