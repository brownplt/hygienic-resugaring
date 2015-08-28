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
resolve = T.resolve
unresolve = T.unresolve
iso = T.iso

_match = S._match
substitute = S.substitute
desugar = S.desugar-full
resugar = S.resugar-full


check "Resolve and Unresolve":
  lam-sig = signature([list: s-empty, s-child(0)], s-empty)
  lam-shadow-sig = signature(
    [list: s-empty, s-empty, s-compose(s-child(1), s-child(0))],
    s-empty)
  app-sig = signature(
    [list: s-empty, s-empty], s-empty)
  sigs = [D.string-dict:
    "lam", lam-sig,
    "lam2", lam-shadow-sig,
    "app", app-sig]

  X = free-var("x")
  Y = free-var("y")
  Z = free-var("z")
  W = free-var("w")

  shadow resolve = lam(t): resolve(sigs, t) end
  shadow unresolve = lam(t): unresolve(sigs, t) end

  fun lam-node(param, body):
    t-node("lam", 0, [list: t-decl(param), body])
  end
  fun lam2-node(param1, param2, body):
    t-node("lam2", 0,
      [list: t-decl(param1), t-decl(param2), body])
  end
  fun app-node(func, arg):
    t-node("app", 0, [list: func, arg])
  end
  term1 = lam-node(X, lam-node(X, t-refn(X)))
  term2 = lam-node(Y, lam-node(Y, t-refn(Y)))
  term3 = lam-node(X, lam-node(Y, t-refn(X)))
  term4 = lam-node(X, lam-node(Y, t-refn(Y)))
  term5 = lam2-node(X, X, t-refn(X))
  term6 = lam2-node(X, Y, lam2-node(Y, Z, t-refn(Y)))
  term7 = lam2-node(X, Y, lam2-node(Y, Z, t-refn(X)))
  term8 = app-node(term4, term7)
  term9 = lam-node(X, lam2-node(Y, X, lam-node(X, t-refn(X))))

  resolve(term1) is%(iso)     resolve(term1)
  resolve(term1) is%(iso)     resolve(term2)
  resolve(term1) is-not%(iso) resolve(term3)
  resolve(term1) is%(iso)     resolve(term4)

  unresolve(resolve(term3)) is term3
  unresolve(resolve(term4)) is term4
  resolve(unresolve(resolve(term1))) is%(iso) resolve(term1)
  resolve(unresolve(resolve(term5))) is%(iso) resolve(term5)
  resolve(unresolve(resolve(term6))) is%(iso) resolve(term6)
  resolve(unresolve(resolve(term7))) is%(iso) resolve(term7)
  resolve(unresolve(resolve(term8))) is%(iso) resolve(term8)
  resolve(unresolve(resolve(term9))) is%(iso) resolve(term9)

  # Example from paper:
  unresolve(
    lam-node(mk-var("msg", 1),
      lam-node(mk-var("port", 2),
        lam-node(mk-var("port", 3),
          app-node(
            t-refn(mk-var("msg", 1)),
            app-node(
              t-refn(mk-var("port", 2)),
              t-refn(mk-var("port", 3))))))))
    .display()
    is "lam($msg, lam($port_2, lam($port_3, app(msg, app(port_2, port_3)))))"

  unresolve(
    lam-node(mk-var("msg", 1),
      lam-node(mk-var("port", 2),
        lam-node(mk-var("port", 3),
          app-node(
            t-refn(mk-var("msg", 1)),
            t-refn(mk-var("port", 2)))))))
    .display()
    is "lam($msg, lam($port_2, lam($port, app(msg, port_2))))"

  unresolve(
    app-node(
      lam-node(mk-var("x", 1), t-refn(mk-var("x", 1))),
      lam-node(mk-var("x", 1), t-refn(mk-var("x", 1)))))
    .display()
    is "app(lam($x, x), lam($x, x))"
end

check "Match/Subs":
  lam-sig = signature([list: s-empty, s-child(0)], s-empty)
  lam2-sig = signature([list: s-empty, s-empty, s-union(s-child(0),
        s-child(1))], s-empty)
  sigs = [D.string-dict: "lam", lam-sig, "lam2", lam2-sig]

  X = free-var("x")
  Y = free-var("y")

  fun lam-node(param, body):
    t-node("lam", 0, [list: param, body])
  end

  fun lam2-node(param1, param2, body):
    t-node("lam2", 0, [list: param1, param2, body])
  end

    term1 = resolve(sigs, lam-node(t-decl(X), lam-node(t-decl(Y),
        t-refn(X))))
  term2 = resolve(sigs, lam2-node(t-decl(X), t-decl(Y), t-refn(X)))
    ctx1  = resolve(sigs, lam-node(t-hole(1), lam-node(t-hole(2),
        t-hole(3))))
  ctx2  = resolve(sigs, lam2-node(t-hole(1), t-hole(2), t-hole(3)))

  substitute(_match(term1, ctx1).value, ctx2) is%(iso) term2
  substitute(_match(term2, ctx2).value, ctx1) is%(iso) term1
  _match(term2, ctx1) is none
end

data Closure:
  | closure(v :: Var, body :: Term, env :: D.StringDict)
sharing:
  _output(self):
    VS.vs-str(self.display())
  end,
  display(self):
    "closure($" + self.v.name + ", " + self.body.display() + ")"
  end,
  _equals(self, other, eq):
    E.NotEquals
  end
end

check "Small Lang Test":
  sigs = [D.string-dict:
    "lam", signature([list: s-empty, s-child(0)], s-empty),
    "app", signature([list: s-empty, s-empty], s-empty),
    "plus", signature([list: s-empty, s-empty], s-empty),
    "or", signature([list: s-empty, s-empty], s-empty),
    "if", signature([list: s-empty, s-empty, s-empty], s-empty),
    "let", signature([list: s-empty, s-empty, s-child(0)], s-empty),
    "num", signature([list: s-empty], s-empty)]

  fun interp(term, env, emit, tagged-emit):
    cases(Term) term:
      | t-val(val) =>
        val
      | t-refn(v)  =>
        tagged-emit(term)
        env.get-value(var-to-str(v))
      | t-tag(left, right, shadow term) =>
        fun frame(t): tagged-emit(t-tag(left, right, t)) end
        interp(term, env, emit, frame)
      | t-node(con, id, ts) =>
        ask:
          | con == "num" then:
            tagged-emit(term)
            interp(ts.get(0), env, emit, emit)
          | con == "plus" then:
                        fun frame-x(t): tagged-emit(t-node(con, id,
                [list: t, ts.get(1)])) end
            x = interp(ts.get(0), env, frame-x, frame-x)
                        fun frame-y(t): tagged-emit(t-node(con, id,
                [list: t-val(x), t])) end
            y = interp(ts.get(1), env, frame-y, frame-y)
            frame-y(t-val(y))
            x + y
          | con == "if" then:
                        fun frame(t): tagged-emit(t-node(con, id,
                [list: t, ts.get(1), ts.get(2)])) end
            cond = interp(ts.get(0), env, frame, frame)
            frame(t-val(cond))
            if cond == 0:
              interp(ts.get(1), env, emit, emit)
            else:
              interp(ts.get(2), env, emit, emit)
            end
          | con == "lam" then:
            tagged-emit(term)
            closure(ts.get(0).v, ts.get(1), env)
          | con == "app" then:
                        fun frame-clos(t): tagged-emit(t-node(con, id,
                [list: t, ts.get(1)])) end
                        clos = interp(ts.get(0), env, frame-clos,
              frame-clos)
                        fun frame-arg(t): tagged-emit(t-node(con, id,
                [list: t-val(clos), t])) end
                        arg  = interp(ts.get(1), env, frame-arg,
              frame-arg)
            frame-arg(t-val(arg))
                        interp(clos.body,
              clos.env.set(var-to-str(clos.v), arg), emit, emit)
        end
    end
  end

  X = free-var("x")
  Y = free-var("y")

  fun num-node(n):
    t-node("num", 0, [list: t-val(n)])
  end
  fun lam-node(param, body):
    t-node("lam", 0, [list: param, body])
  end
  fun app-node(func, arg):
    t-node("app", 0, [list: func, arg])
  end
  fun plus-node(left, right):
    t-node("plus", 0,[list: left, right])
  end
  fun if-node(cond, consq, altern):
    t-node("if", 0, [list: cond, consq, altern])
  end
  fun let-node(param, val, body):
    t-node("let", 0, [list: param, val, body])
  end

  fun desugar-let(ctx):
    app-node(lam-node(ctx.get(0), ctx.get(2)), ctx.get(1))
  end

  fun desugar-or(ctx):
    let-node(t-decl(X), ctx.get(0), if-node(t-refn(X), t-refn(X),
        ctx.get(1)))
  end

  fun desugar-plus(ctx):
    ctx
  end

  sugar = [D.string-dict:
    "let", desugar-let,
    "or",  desugar-or,
    "plus", desugar-plus]

  primary = [list: "let", "or", "plus", "lam", "app", "if"]
  
  term1 = resolve(sigs, app-node(
      if-node(num-node(17), num-node(17),
        lam-node(t-decl(X), plus-node(t-refn(X), num-node(1)))),
      num-node(2)))

  var STEPS = [list:]
  fun show-core-step(t):
    STEPS := STEPS + [list: t.display()]
  end
  fun show-surf-step(t):
    cases(Option) resugar(sigs, sugar, t):
      | none           => nothing
      | some(shadow t) =>
        STEPS := STEPS + [list: t.display()]
    end
  end

  # Test the core stepper for sanity
    interp(term1, D.make-string-dict(), show-core-step,
    show-core-step)
  STEPS.get(0) is "app(if(num(<17>), num(<17>), lam($x, plus(x, num(<1>)))), num(<2>))"
  STEPS.get(1) is "app(if(<17>, num(<17>), lam($x, plus(x, num(<1>)))), num(<2>))"
  STEPS.get(2) is "app(lam($x, plus(x, num(<1>))), num(<2>))"
  STEPS.get(3) is "app(<closure($x, plus(x, num(<1>)))>, num(<2>))"
  STEPS.get(4) is "app(<closure($x, plus(x, num(<1>)))>, <2>)"
  STEPS.get(5) is "plus(x, num(<1>))"
  STEPS.get(6) is "plus(<2>, num(<1>))"
  STEPS.get(7) is "plus(<2>, <1>)"

  term2 = resolve(sigs,
    let-node(t-decl(X), num-node(3), t-refn(X)))
  term2-expected = resolve(sigs,
    app-node(lam-node(t-decl(X), t-refn(X)), num-node(3)))
  desugar(sigs, sugar, term2).strip-tags() is%(iso) term2-expected

  term3 = resolve(sigs,
    let-node(t-decl(X), num-node(5),
      let-node(t-decl(Y), plus-node(num-node(-6), t-refn(X)),
        let-node(t-decl(X), plus-node(t-refn(X), t-refn(Y)),
          plus-node(t-refn(X), t-refn(Y))))))
  term3-des = desugar(sigs, sugar, term3)

  # Test resugaring
  STEPS := [list:]
    interp(term3-des, D.make-string-dict(), show-surf-step,
    show-surf-step)
  # extremely fragile test; should really be agnostic to id
    STEPS.get(0) is "let($x, num(<5>), let($y, plus(num(<-6>), x), let($x_219, plus(x, y), plus(x_219, y))))"
    STEPS.get(1) is "let($y, plus(num(<-6>), x), let($x, plus(x, y), plus(x, y)))"
  STEPS.get(2) is "let($x, plus(x, y), plus(x, y))"
  STEPS.get(3) is "plus(x, y)"
  STEPS.get(4) is "plus(<4>, y)"
  STEPS.get(5) is "plus(<4>, <-1>)"
end

# Incomplete:
check "Lang Test":
  sigs = [D.string-dict:
    "lam", signature([list: s-empty, s-child(0)], s-empty),
    "app", signature([list: s-empty, s-empty], s-empty),
    "let", signature([list: s-empty, s-child(0)], s-empty),
    "args", signature([list: s-empty, s-empty], s-empty),
    "lam-bind", signature([list: s-empty, s-empty],
      s-union(s-child(0), s-child(1))),
    "let-bind", signature([list: s-empty, s-empty, s-empty],
      s-union(s-child(0), s-child(2))),
    "let-rec-bind", signature(
      [list: s-empty, s-union(s-child(0), s-child(2)), s-child(0)],
      s-union(s-child(0), s-child(2))),
    "let-star-bind", signature([list: s-empty, s-empty, s-child(0)],
      s-union(s-child(0), s-child(2))),
    "no-bind", signature([list:], s-empty)]

  #  fun desugar-let(ctx :: Term) -> Term:
  #    t-node("app", 0, [list: let-binds-to-lam-binds(ctx.get(0)),
  #    ctx])
  #  end

  nothing
end