provide *
provide-types *
import string-dict as D
import sets as SET
import srcloc as S
import valueskeleton as VS
import "util.arr" as U
import "atom.arr" as A

try-opt = U.try-opt
try-opts = U.try-opts
try-bool-opt = U.try-bool-opt
try-opt-map2 = U.try-opt-map2

type Var = A.Var
type Id = A.Id
type Permutation = A.Permutation
var-to-str = A.var-to-str
str-to-var = A.str-to-var
fresh-id = A.fresh-id
permute-id = A.permute-id
permute-var = A.permute-var
p-empty = A.p-empty
p-var-swap = A.p-var-swap
p-compose = A.p-compose
p-union = A.p-union


### Terms       ###
### (Section 3) ###

# Represents both Terms and Contexts
# Terms can't have t-hole, and Contexts can't have t-tag.
data Term:
  | t-decl(v :: Var)
  | t-refn(v :: Var)
  | t-val(val :: Any)
  | t-node(con :: String, id :: Id, subterms :: List<Term>)
    with:
    get(self, n):
      self.subterms.get(n)
    end
  | t-hole(index :: Number)
  | t-tag(lhs :: Term, rhs :: Term, term :: Term)
sharing:
  _output(self):
    VS.vs-str(self.display())
  end,
  display(self):
    cases(Term) self:
      | t-decl(v)       => "$" + v.display()
      | t-refn(v)       => v.display()
      | t-val(val)      => "<" + tostring(val) + ">"
      | t-hole(i)       => "@" + tostring(i)
      | t-node(con, _, ts) =>
        con + "(" + map(lam(x): x.display() end, ts).join-str(", ") + ")"
      | t-tag(left, right, term) =>
        "TAG[" + left.display() + ", " + right.display() + "] " + term.display()
    end
  end,
  strip-tags(self):
    cases(Term) self:
      | t-decl(_)           => self
      | t-refn(_)           => self
      | t-val(_)            => self
      | t-hole(_)           => self
      | t-node(con, id, ts) => t-node(con, id, map(_.strip-tags(), ts))
      | t-tag(_, _, term)   => term.strip-tags()
    end
  end
end

# Figure 2
fun permute-term(bij :: Permutation, t :: Term) -> Term:
  cases(Term) t:
    | t-decl(v)      => t-decl(permute-var(bij, v))
    | t-refn(v)      => t-refn(permute-var(bij, v))
    | t-val(_)       => t
    | t-hole(i)      => t
    | t-node(con, id, ts) =>
      t-node(con, permute-id(bij, id), map(permute-term(bij, _), ts))
    | t-tag(lhs, rhs, shadow t) =>
      t-tag(
        permute-term(bij, lhs),
        permute-term(bij, rhs),
        permute-term(bij, t))
  end
end


### Signatures    ###
### (Section 3.4) ###

data Sig:
  | s-empty
  | s-child(child :: Number)
  | s-compose(sig1 :: Sig, sig2 :: Sig)
  | s-union(sig1 :: Sig, sig2 :: Sig)
end

# Figure 3
fun apply-sig(sig :: Sig, outs :: List<Permutation>) -> Permutation:
  cases(Sig) sig:
    | s-empty               => p-empty
    | s-child(i)            => outs.get(i)
    | s-compose(sig1, sig2) =>
      p-compose(apply-sig(sig1, outs), apply-sig(sig2, outs))
    | s-union(sig1, sig2)   =>
      opt = p-union(apply-sig(sig1, outs), apply-sig(sig2, outs))
      cases(Option) opt:
        | some(bij) => bij
        | none      =>
          raise("Overlapping variable declarations when applying scope signature.")
      end
  end
end

# Figure 3
fun apply-sig-set(sig :: Sig, ls :: List<Set>) -> Set:
  cases(Sig) sig:
    | s-empty    => SET.empty-list-set
    | s-child(i) => ls.get(i)
    | s-compose(sig1, sig2) =>
      apply-sig-set(sig1, ls).union(apply-sig-set(sig2, ls))
    | s-union(sig1, sig2) =>
      apply-sig-set(sig1, ls).union(apply-sig-set(sig2, ls))
  end
end

data Signature:
  | signature(childs :: List<Sig>, out :: Sig)
end

type SignatureSet = D.StringDict<Signature>

data TermOut:
  | term-out(term :: Term, out :: Permutation)
end

# Figure 4
fun resolve(ss :: SignatureSet, t :: Term) -> Term:
  # TODO: Notice that this doesn't check for unbound variables.
  #       This is in line with the paper,
  #       and doesn't technically violate any theorems,
  #       but a full implementation should check and give error
  #       messages.
  fun recur(shadow t :: Term) -> TermOut:
    cases(Term) t:
      | t-decl(v) =>
        old-var = v
        new-var = v.freshen()
        term-out(t-decl(new-var), p-var-swap(old-var, new-var))
      | t-refn(v) => term-out(t, p-empty)
      | t-val(_)  => term-out(t, p-empty)
      | t-hole(i) => term-out(t, p-empty)
      | t-node(con, id, ts) =>
        sig = cases(Option) ss.get(con):
          | none => raise("No signature found for " + con)
          | some(sig) => sig
        end
        tos = map(recur, ts)
        os = map(_.out, tos)
        shadow ts = map(_.term, tos)
        shadow ts = for map_n(n from 0, shadow t from ts):
          permute-term(apply-sig(sig.childs.get(n), os), t)
        end
        term-out(t-node(con, fresh-id(), ts), apply-sig(sig.out, os))
      | t-tag(left, right, shadow t) =>
        t-o = recur(t)
        cases(Option) validate(t-o.term, right):
          | some(shadow right) =>
            term-out(t-tag(left, right, t-o.term), t-o.out)
          | none =>
            # This is a failure case: resugaring will fail here
            term-out(t-tag(left, right, t-o.term), t-o.out)
        end
    end
  end
  fun validate(shadow t :: Term, ctx :: Term) -> Option<Term>:
    ask:
      | is-t-hole(ctx) then:
        some(ctx)
      | is-t-val(t) and is-t-val(ctx) then:
        for try-bool-opt(_ from t.val == ctx.val):
          some(t)
        end
      | is-t-decl(t) and is-t-decl(ctx) then:
        for try-bool-opt(_ from t.v.name == ctx.v.name):
          some(t)
        end
      | is-t-refn(t) and is-t-refn(ctx) then:
        for try-bool-opt(_ from t.v.name == ctx.v.name):
          some(t)
        end
      | is-t-node(t) and is-t-node(ctx) then:
        for try-bool-opt(_ from t.con == ctx.con):
          for try-bool-opt(_ from t.subterms.length() == ctx.subterms.length()):
            for try-opt(subterms from
                for try-opt-map2(
                    shadow t from t.subterms,
                    shadow ctx from ctx.subterms):
                  validate(t, ctx)
                end):
              some(t-node(t.con, t.id, subterms))
            end
          end
        end
      | otherwise: none
    end
  end
  recur(t).term
end

# Figure 4
fun unresolve(ss :: SignatureSet, t :: Term) -> Term:
  # TODO: Make this efficient
  fun lookup-sig(con :: String) -> Signature:
    cases(Option) ss.get(con):
      | none => raise("No signature found for " + con)
      | some(sig) => sig
    end
  end
  fun exports(shadow t :: Term) -> SET.Set<Var>:
    cases(Term) t:
      | t-decl(v) => [SET.list-set: v]
      | t-refn(v) => SET.empty-list-set
      | t-hole(i) => #SET.empty-list-set
        raise("Scope unresolution: cannot unresolve hole")
      | t-val(_)  => SET.empty-list-set
      | t-node(con, _, ts) =>
        sig = lookup-sig(con)
        apply-sig-set(sig.out, map(exports, ts))
    end
  end
    fun find-threats(shadow t :: Term, s :: SET.Set<Var>) ->
    SET.Set<Var>:
    cases(Term) t:
      | t-decl(v) => SET.empty-list-set
      | t-refn(v) =>
        threatened = for any(v2 from s.to-list()):
          (v.name == v2.name) and (v.id <> v2.id)
        end
        if threatened:
          [SET.list-set: v]
        else:
          SET.empty-list-set
        end
      | t-hole(i) => SET.empty-list-set
      | t-val(_)  => SET.empty-list-set
      | t-node(con, id, ts) =>
        sig = lookup-sig(con)
        os = map(exports, ts)
        for fold2(result from SET.empty-list-set,
            shadow t from ts,
            shadow sig from sig.childs):
                    result.union(find-threats(t,
              s.union(apply-sig-set(sig, os))))
        end
    end
  end
  fun rename-threats(shadow t :: Term, threats):
    fun rename(v):
      cases(Option) threats.get(var-to-str(v)):
        | none      => v.unfreshen()
        | some(str) => str-to-var(str)
      end
    end
    cases(Term) t:
      | t-decl(v)  => t-decl(rename(v))
      | t-refn(v)  => t-refn(rename(v))
      | t-hole(i)  => #t-hole(i)
        raise("Scope unresolution: cannot unresolve hole")
      | t-val(val) => t-val(val)
      | t-node(con, id, ts) =>
        t-node(con, 0, map(rename-threats(_, threats), ts))
    end
  end
  vs = find-threats(t, SET.empty-list-set)
  f = for fold(f from D.make-string-dict(), v from vs.to-list()):
    f.set(var-to-str(v), var-to-str(v.rename()))
  end
  renamed = rename-threats(t, f)
  renamed
end

### Isomorphism      ###
### (Definition 1)   ###
fun iso(t1 :: Term, t2 :: Term) -> Boolean:
  is-some(find-iso(t1, t2))
end

fun find-iso(t1 :: Term, t2 :: Term) -> Option<Permutation>:
  when is-t-tag(t1) or is-t-tag(t2):
    raise("Isomorphism checking: cannot compare tagged terms.")
  end
  ask:
    | is-t-decl(t1) and is-t-decl(t2) then:
      some(p-var-swap(t1.v, t2.v))
    | is-t-refn(t1) and is-t-refn(t2) then:
      some(p-var-swap(t1.v, t2.v))
    | is-t-hole(t1) and is-t-hole(t2) then:
      for try-bool-opt(_ from t1.index == t2.index):
        some(p-empty)
      end
    | is-t-val(t1) and is-t-val(t2) then:
      for try-bool-opt(_ from t1.val == t2.val):
        some(p-empty)
      end
    | is-t-node(t1) and is-t-node(t2) then:
      for try-bool-opt(_ from t1.con == t2.con):
                for try-bool-opt(_ from t1.subterms.length() ==
              t2.subterms.length()):
                    for try-opts(bij from p-empty, n from range(0,
                t1.subterms.length())):
                        for try-opt(bij2 from
                        find-iso(t1.subterms.get(n),
                  t2.subterms.get(n))):
              p-union(bij, bij2)
            end
          end
        end
      end
    | otherwise:
      none
  end
end