import Base
import ../lib/foundation.bend as F

def equal_rows(a: List<&2, F.Pair2<String, Nat>>, b: List<&2, F.Pair2<String, Nat>>) -> Bool:
  match a b:
    case Nil{} Nil{}: True{}
    case F.Pair2{ka, va} <> aa F.Pair2{kb, vb} <> bb:
      Bool.and(String.eq(ka, kb), Bool.and(Nat.is_eq(va, vb), equal_rows(aa, bb)))
    case other other2: False{}

def equal_value(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Bool:
  match a b:
    case None{} None{}: True{}
    case Some{a} Some{b}: Nat.is_eq(a, b)
    case other other2: False{}

def before(a: String, b: String) -> Bool:
  Cmp.is_lt(String.order(a, b))

def lower_ok(bound: Maybe<&2, String>, key: String) -> Bool:
  match bound:
    case None{}: True{}
    case Some{bound}: before(bound, key)

def upper_ok(bound: Maybe<&2, String>, key: String) -> Bool:
  match bound:
    case None{}: True{}
    case Some{bound}: before(key, bound)

def valid(tree: F.Global.map<Nat>, +lo: Maybe<&2, String>, +hi: Maybe<&2, String>) -> Bool:
  match tree:
    case F.Global.Leaf{}: True{}
    case F.Global.Node{height, +key, value, +left, +right}:
      +lh = F.Global.height(Nat, left)
      +rh = F.Global.height(Nat, right)
      Bool.and(Nat.is_eq(height, (1n + Nat.max(lh, rh) : Nat)),
        Bool.and(Nat.is_le(lh, (rh + 1n : Nat)), Bool.and(Nat.is_le(rh, (lh + 1n : Nat)),
          Bool.and(lower_ok(lo, key), Bool.and(upper_ok(hi, key),
            Bool.and(valid(left, lo, Some{key}), valid(right, Some{key}, hi)))))))

def all_found(rows: List<&2, F.Pair2<String, Nat>>, +tree: F.Global.map<Nat>) -> Bool:
  match rows:
    case Nil{}: True{}
    case F.Pair2{name, value} <> rest:
      Bool.and(equal_value(F.Global.map_lookup(Nat, name, tree), Some{value}), all_found(rest, tree))

def same(+tree: F.Global.map<Nat>, +reference: List<&2, F.Pair2<String, Nat>>) -> Bool:
  Bool.and(valid(tree, None{}, None{}),
    Bool.and(equal_rows(F.Global.map_rows(Nat, tree, Nil{}), reference),
      Bool.and(all_found(reference, tree),
        Bool.and(equal_value(F.Global.map_lookup(Nat, "!", tree), None{}), equal_value(F.Global.map_lookup(Nat, "zzzz", tree), None{})))))

def history(rows: List<&2, F.Pair2<String, Nat>>, tree: F.Global.map<Nat>, reference: List<&2, F.Pair2<String, Nat>>) -> Bool:
  match rows:
    case Nil{}: same(tree, reference)
    case F.Pair2{+name, +value} <> rest:
      +next = F.Global.map_put(Nat, name, value, tree)
      +expected = F.Global.put(Nat, name, value, reference)
      Bool.and(same(next, expected), history(rest, next, expected))

def sequence(count: Nat, +mode: Nat) -> List<&2, F.Pair2<String, Nat>>:
  match count:
    case 0n: Nil{}
    case 1n+ +rest:
      F.Pair2{F.Text.nat(((rest * mode : Nat) % 257n : Nat)), rest} <> sequence(rest, mode)

def raw_table() -> Bool:
  +rows : List<&2, F.Pair2<String, Nat>> = [F.Pair2{"z", 1n}, F.Pair2{"a", 2n}, F.Pair2{"z", 3n}]
  +table = F.Global.table_from_rows(Nat, rows)
  +updated = F.Global.table_put(Nat, "z", 4n, table)
  Bool.and(equal_rows(F.Global.table_rows(Nat, table), rows),
    Bool.and(equal_value(F.Global.table_lookup(Nat, "z", table), Some{1n}),
      Bool.and(equal_rows(F.Global.table_rows(Nat, updated), [F.Pair2{"z", 4n}, F.Pair2{"a", 2n}, F.Pair2{"z", 3n}]),
        equal_value(F.Global.table_lookup(Nat, "z", updated), Some{4n}))))

def rotations() -> Bool:
  Bool.and(history([F.Pair2{"c", 1n}, F.Pair2{"b", 2n}, F.Pair2{"a", 3n}], F.Global.Leaf{}, Nil{}),
    Bool.and(history([F.Pair2{"a", 1n}, F.Pair2{"b", 2n}, F.Pair2{"c", 3n}], F.Global.Leaf{}, Nil{}),
      Bool.and(history([F.Pair2{"c", 1n}, F.Pair2{"a", 2n}, F.Pair2{"b", 3n}], F.Global.Leaf{}, Nil{}),
        history([F.Pair2{"a", 1n}, F.Pair2{"c", 2n}, F.Pair2{"b", 3n}], F.Global.Leaf{}, Nil{}))))

def finish(ok: Bool) -> IO(Unit):
  match ok:
    case True{}: IO.print("GLOBAL-MAP pass=6 fail=0 (four rotations, 1800 prefixes, raw rows)")
    case False{}: IO.die(Unit, 1, "GLOBAL-MAP FAIL")

def main() -> IO(Unit):
  finish(Bool.and(same(F.Global.Leaf{}, Nil{}), Bool.and(rotations(),
    Bool.and(history(sequence(600n, 1n), F.Global.Leaf{}, Nil{}),
      Bool.and(history(sequence(600n, 256n), F.Global.Leaf{}, Nil{}),
        Bool.and(history(sequence(600n, 73n), F.Global.Leaf{}, Nil{}), raw_table()))))))
