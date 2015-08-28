provide *
provide-types *
import valueskeleton as VS
import string-dict as D
import "util.arr" as U

try-opts = U.try-opts

### Atoms       ###
### (Section 3) ###

type Name = String
type Id = Number # zero means 'free'

var NEXT_ID = 0

fun fresh-id():
  NEXT_ID := NEXT_ID + 1
  NEXT_ID
end

fun reset-ids():
  NEXT_ID := 0
end

data Var:
  | mk-var(name :: Name, id :: Id)
sharing:
  _output(self):
    VS.vs-str(self.name)
  end,
  display(self):
    self.name
  end,
  freshen(self):
    mk-var(self.name, fresh-id())
  end,
  unfreshen(self):
    mk-var(self.name, 0)
  end,
  rename(self):
    if self.id == 0:
      self
    else:
      mk-var(self.name + "_" + tostring(self.id), 0)
    end
  end
end

fun free-var(name :: Name) -> Var:
  mk-var(name, 0)
end

fun var-to-str(v :: Var) -> String:
  v.name + ":" + num-to-string(v.id)
end

fun str-to-var(str :: String) -> Var:
  parts = string-split(str, ":")
  mk-var(parts.get(0), string-to-number(parts.get(1)).value)
end


### Permutations  ###
### (Section 3.1) ###
### (Figure 2)    ###

type Permutation = D.StringDict<String>

fun permute-var(p :: Permutation, v :: Var) -> Var:
  cases(Option) p.get(var-to-str(v)):
    | none      => v
    | some(str) => str-to-var(str)
  end
end

fun permute-id(p :: Permutation, id :: Id) -> Id:
  cases(Option) p.get(num-to-string(id)):
    | none      => id
    | some(str) => string-to-number(str).value
  end
end

p-empty = D.make-string-dict()

fun p-inverse(p :: Permutation) -> Permutation:
    for fold(inv from D.make-string-dict(), key from
      p.keys().to-list()):
    inv.set(key, p.get-value(key))
  end
end

fun p-node-swap(id1 :: Id, id2 :: Id) -> Permutation:
  shadow id1 = num-to-string(id1)
  shadow id2 = num-to-string(id2)
  if id1 == id2:
    p-empty
  else:
    D.make-string-dict()
      .set(id1, id2)
      .set(id2, id1)
  end
end

fun p-var-swap(v1 :: Var, v2 :: Var) -> Permutation:
  shadow v1 = var-to-str(v1)
  shadow v2 = var-to-str(v2)
  if v1 == v2:
    p-empty
  else:
    D.make-string-dict()
      .set(v1, v2)
      .set(v2, v1)
  end
end

fun p-compose(p1 :: Permutation, p2 :: Permutation) -> Permutation:
  fun apply(p, x):
    cases(Option) p.get(x):
      | none    => x
      | some(y) => y
    end
  end
  domain = p1.keys().union(p2.keys()).to-list()
  for fold(comp from p-empty, key from domain):
    comp.set(key, apply(p2, apply(p1, key)))
  end
end

fun p-union(p1 :: Permutation, p2 :: Permutation) ->
  Option<Permutation>:
  fun apply(p, x):
    cases(Option) p.get(x):
      | none    => x
      | some(y) => y
    end
  end
  domain = p1.keys().union(p2.keys()).to-list()
  for try-opts(union from p-empty, key from domain):
    x = p1.get(key)
    y = p2.get(key)
    if is-none(x):
      some(union.set(key, y.value))
    else if is-none(y):
      some(union.set(key, x.value))
    else if x.value == y.value:
      some(union.set(key, x.value))
    else:
      none
    end
  end
end


### Tests ###

check:
  x1 = mk-var("x", 1)
  y2 = mk-var("y", 2)
  y3 = mk-var("y", 3)

  p1 = p-node-swap(1, 2)
  p2 = p-var-swap(x1, y2)
  p3 = p-var-swap(y3, y2)

  p-union(p-compose(p1, p2), p3) is none

  p = p-union(p1, p2)
  p satisfies is-some
  shadow p = p-compose(p.value, p3)
  permute-var(p, x1) is y3
  permute-var(p, y2) is x1
  permute-var(p, y3) is y2
  permute-var(p, mk-var("x", 3)) is mk-var("x", 3)
  permute-id(p, 1) is 2
  permute-id(p, 2) is 1
  permute-id(p, 3) is 3
end