provide *
provide-types *
import equality as E


fun bool-to-eq(b):
  if b:
    E.Equal
  else:
    E.NotEqual("")
  end
end

fun bool-opt(bool):
  if bool:
    some(nothing)
  else:
    none
  end
end

fun try-opt(func, opt):
  cases(Option) opt:
    | none      => none
    | some(val) => func(val)
  end
end

fun try-bool-opt(func, bool):
  if bool:
    func(nothing)
  else:
    none
  end
end

fun try-opts(func, default, lst):
  for fold(res from some(default), elem from lst):
    cases(Option) res:
      | none      => none
      | some(val) => func(val, elem)
    end
  end
end

fun try-opt-map(func, lst):
  for fold(res from some([list:]), elem from lst):
    for try-opt(shadow res from res):
      for try-opt(shadow elem from func(elem)):
        some(link(elem, res))
      end
    end
  end.and-then(_.reverse())
end

fun try-opt-map2(func, lst1, lst2):
  for fold2(res from some([list:]), elem1 from lst1, elem2 from lst2):
    for try-opt(shadow res from res):
      for try-opt(shadow elem from func(elem1, elem2)):
        some(link(elem, res))
      end
    end
  end.and-then(_.reverse())
where:
  for try-opt-map2(x from [list: 1, 2], y from [list: 10, 20]):
    some(x + y + 1)
  end
    is some([list: 12, 23])
end

fun dict-union(d1, d2):
  for fold(d from d1, key from d2.keys().to-list()):
    d.set(key, d2.get-value(key))
  end
end
