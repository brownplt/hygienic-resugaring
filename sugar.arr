provide *
provide-types *
import string-dict as D
import "util.arr" as U
import "term.arr" as T

try-opt = U.try-opt
try-opts = U.try-opts
dict-union = U.dict-union
try-bool-opt = U.try-bool-opt

type Term = T.Term
type SignatureSet = T.SignatureSet
resolve = T.resolve
t-node = T.t-node
t-hole = T.t-hole
t-tag = T.t-tag
is-t-node = T.is-t-node
is-t-tag = T.is-t-tag
is-t-refn = T.is-t-refn
is-t-val = T.is-t-val
is-t-hole = T.is-t-hole
is-t-decl = T.is-t-decl


### Match & Substitute ###
### (Section 4.1)      ###

type Subs = D.StringDict<Term>

fun subs-union(s1 :: Subs, s2 :: Subs) -> Option<Subs>:
    repetition = for fold(repetition from false, key from s2.keys().to-list()):
    repetition or s1.has-key(key)
  end
  if repetition:
    none
  else:
    some(dict-union(s1, s2))
  end
end

# Figure 6
fun _match(t :: Term, ctx :: Term) -> Option<Subs>:
  fun match-check-same(bool):
    if bool:
      some(D.make-string-dict())
    else:
      none
    end
  end
  ask:
    | is-t-hole(ctx) then:
      some([D.string-dict: num-to-string(ctx.index), t])
    | is-t-decl(t) and is-t-decl(ctx) then:
      match-check-same(t.v == ctx.v)
    | is-t-refn(t) and is-t-refn(ctx) then:
      match-check-same(t.v == ctx.v)
    | is-t-val(t) and is-t-val(ctx) then:
      match-check-same(t.val == ctx.val)
    | is-t-node(t) and is-t-node(ctx) then:
      for try-bool-opt(_ from t.con == ctx.con):
        for try-bool-opt(_ from t.subterms.length() == ctx.subterms.length()):
          for try-opts(
              res from D.make-string-dict(),
              n from range(0, t.subterms.length())):
            for try-opt(res2 from _match(t.subterms.get(n), ctx.subterms.get(n))):
              subs-union(res, res2)
            end
          end
        end
      end
    | otherwise:
      none
  end
end

# Figure 5
fun substitute(subs :: Subs, ctx :: Term) -> Term:
  cases(Term) ctx:
    | t-hole(i) => subs.get-value(num-to-string(i))
    | t-decl(_) => ctx
    | t-refn(_) => ctx
    | t-val(_)  => ctx
    | t-node(con, id, ctxs) =>
      t-node(con, id, map(substitute(subs, _), ctxs))
    | t-tag(_, _, _) =>
      raise("Substitute: cannot substitute into tagged term.")
  end
end


### Desugar & Resugar ###
### (Section 4.2)     ###

type Sugar = D.StringDict<(Term -> Term)>

fun head-of-term(sugar :: Sugar, con, id, ts) -> Term:
  var hole-id = 0
  fun new-hole():
    hole-id := hole-id + 1
    t-hole(hole-id)
  end
  fun is-primary(shadow con):
    cases(Option) sugar.get(con):
      | some(_) => true
      | none    => false
    end
  end
  fun recur(t :: Term):
    cases(Term) t:
      | t-decl(_) => new-hole()
      | t-refn(_) => new-hole()
      | t-val(_)  => new-hole()
      | t-node(shadow con, shadow id, shadow ts) =>
        if is-primary(con):
          new-hole()
        else:
          t-node(con, id, map(recur, ts))
        end
      | t-tag(_, _, _) =>
        raise("Head: cannot take the head of tagged term.")
    end
  end
  t-node(con, id, map(recur, ts))
end

# Figure 7
fun desugar-full(ss :: SignatureSet, sugar :: Sugar, t :: Term) -> Term:
  desugar(ss, sugar, resolve(ss, t))
end

data Expansion:
  | SomeExp(lhs, rhs)
  | NoExp
end

fun desugar(ss :: SignatureSet, sugar :: Sugar, t :: Term) -> Term:
  fun desugar-subs(subs):
        for fold(result from D.make-string-dict(), key from subs.keys().to-list()):
      result.set(key, desugar(ss, sugar, subs.get-value(key)))
    end
  end
  fun expand(con, id, ts) -> Expansion:
    cases(Option) sugar.get(con):
      | some(rule) =>
        lhs-ctx = head-of-term(sugar, con, id, ts)
        rhs-ctx = resolve(ss, rule(lhs-ctx))
        SomeExp(lhs-ctx, rhs-ctx)
      | none       =>
        NoExp
    end
  end
  cases(Term) t:
    | t-decl(_) => t
    | t-refn(_) => t
    | t-val(_)  => t
    | t-node(con, id, ts) =>
      cases(Expansion) expand(con, id, ts):
        | NoExp => t-node(con, id, map(desugar(ss, sugar, _), ts))
        | SomeExp(lhs, rhs) =>
          subs = _match(t, lhs).value
          new-term = substitute(desugar-subs(subs), rhs)
          t-tag(lhs, rhs, new-term)
      end
    | t-tag(_, _, _) =>
      raise("Desugar: unexpected tagged term.")
  end
end

# Figure 8
fun resugar-full(ss :: SignatureSet, sugar :: Sugar, t :: Term) ->
  Option<Term>:
  for try-opt(shadow t from resugar(sugar, resolve(ss, t))):
    some(T.unresolve(ss, t))
  end
end

fun resugar(sugar :: Sugar, t :: Term) -> Option<Term>:
  fun resugar-subs(subs):
    for fold(result from some(D.make-string-dict()),
        key from subs.keys().to-list()):
      cases(Option) result:
        | none => none
        | some(shadow result) =>
          cases(Option) resugar(sugar, subs.get-value(key)):
            | none => none
            | some(shadow t) => some(result.set(key, t))
          end
      end
    end
  end
  cases(Term) t:
    | t-decl(_) => some(t)
    | t-refn(_) => some(t)
    | t-val(_)  => some(t)
    | t-node(con, id, ts) => none
    | t-tag(lhs, rhs, shadow t) =>
      cases(Option) _match(t, rhs):
        | none       => none
        | some(subs) =>
          cases(Option) resugar-subs(subs):
            | none => none
            | some(shadow subs) => some(substitute(subs, lhs))
          end
      end
  end
end