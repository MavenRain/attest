"""Small lexical helpers for Bend source policy checks, not a type checker."""
from pathlib import Path
import re

ROOTS = ("lib", "surface", "bin", "erase", "test", "dev")
TOKENS = re.compile(r'"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|//[^\n]*|\#[^\n]*')
DEFINITION = re.compile(r"^(?:@unsafe\s+)?def\s+([\w.]+)\b")
ARM = re.compile(r"(\s*)case\s+([^:]+):")
VARIABLE = re.compile(r"[+&]?[a-z_]\w*")
CONSTRUCTOR = re.compile(r"([\w.]+)\{(.*)\}", re.S)
OPEN = {"{": "}", "(": ")", "[": "]"}

def paths(root):
    return sorted(path for folder in ROOTS for path in (root / folder).rglob("*.bend"))

def code(text):
    return TOKENS.sub(lambda match: "".join("\n" if c == "\n" else " " for c in match.group()), text)

def split_top(text, separators):
    """Split text on separator characters outside braces, parentheses and brackets."""
    def step(state, char):
        parts, current, depth = state
        at_top = depth == 0 and char in separators
        depth = depth + (char in OPEN) - (char in OPEN.values())
        return (parts + [current], "", depth) if at_top else (parts, current + char, depth)
    parts, current, _ = __import__("functools").reduce(step, text, ([], "", 0))
    return [part for part in parts + [current] if part.strip()]

def join_parts(parts):
    """Rejoin `head <> tail` list patterns and `Nn+ pred` successor patterns that a whitespace split cut apart."""
    def open_end(text):
        return text.endswith("<>") or re.fullmatch(r"\d+n\+", text) is not None
    def step(acc, part):
        glue = bool(acc) and (part == "<>" or open_end(acc[-1]))
        return acc[:-1] + [acc[-1] + " " + part] if glue else acc + [part]
    return __import__("functools").reduce(step, parts, [])

def arm_parts(pattern):
    return join_parts([part.strip() for part in split_top(pattern.strip(), " \t,")])

def is_variable(part):
    return VARIABLE.fullmatch(part) is not None

def cons_tree(items):
    """Build the Con/Nil tree of `a <> b <> tail` (tail given) from the parsed items."""
    return __import__("functools").reduce(lambda tail, head: ("ctor", "Con", (head, tail)), reversed(items[:-1]), items[-1])

def tree(part):
    """Parse one pattern into ("var",), ("ctor", name, fields), ("nat", n), ("succ", n, pred) or ("lit", text)."""
    text = part.strip()
    cons = split_top(text.replace("<>", "\0"), "\0")
    shape = CONSTRUCTOR.fullmatch(text)
    successor = re.fullmatch(r"(\d+)n\+\s*(.+)", text, re.S)
    nat = re.fullmatch(r"(\d+)n", text)
    enclosed = text[1:-1] if text[:1] in "[(" and OPEN.get(text[:1]) == text[-1:] else None
    fields = [tree(field) for field in split_top(enclosed or "", ",")]
    return (cons_tree([tree(item) for item in cons]) if len(cons) > 1
            else ("var",) if is_variable(text)
            else ("ctor", shape.group(1).split(".")[-1], tuple(tree(field) for field in split_top(shape.group(2), ",")))
            if shape
            else ("succ", int(successor.group(1)), tree(successor.group(2))) if successor
            else ("nat", int(nat.group(1))) if nat
            else cons_tree(fields + [("ctor", "Nil", ())]) if text[:1] == "["
            else ("ctor", "Tuple", tuple(fields)) if text[:1] == "("
            else ("lit", text))

def overlaps(left, right):
    """True when some value matches both pattern trees."""
    kinds = (left[0], right[0])
    return (True if "var" in kinds
            else len(left[2]) == len(right[2]) and left[1] == right[1] and all(map(overlaps, left[2], right[2]))
            if kinds == ("ctor", "ctor")
            else left[1] == right[1] if kinds in (("nat", "nat"), ("lit", "lit"))
            else right[1] >= left[1] and overlaps(left[2], ("nat", right[1] - left[1])) if kinds == ("succ", "nat")
            else overlaps(right, left) if kinds == ("nat", "succ")
            else overlaps(left[2], right[2]) if kinds == ("succ", "succ") and left[1] == right[1]
            else overlaps(right[2], ("succ", left[1] - right[1], left[2])) if kinds == ("succ", "succ")
            and left[1] > right[1]
            else overlaps(right, left) if kinds == ("succ", "succ")
            else False)

def catch_all(parts, previous):
    """A top-level variable part, or an arm that overlaps an earlier arm of the block on every position."""
    trees = [tree(part) for part in parts]
    return any(map(is_variable, parts)) or any(
        len(arm) == len(trees) and all(map(overlaps, arm, trees)) for arm in previous)

def policy_sites(root):
    result = {"catchalls": [], "unsafe": []}
    for path in paths(root):
        function = ""
        pending = False
        arms = {}
        for line in code(path.read_text()).splitlines():
            stripped = line.strip()
            definition = DEFINITION.match(line)
            pending = pending or stripped.startswith("@unsafe")
            if definition:
                function = definition.group(1)
                if pending:
                    result["unsafe"].append({"path": str(path.relative_to(root)), "function": function})
                pending = False
            arm = ARM.match(line)
            indent = len(line) - len(line.lstrip())
            arms = {level: rows for level, rows in arms.items()
                    if (level <= indent if arm else level < indent) or not stripped}
            if arm:
                parts = arm_parts(arm.group(2))
                if parts and catch_all(parts, arms.get(indent, [])):
                    result["catchalls"].append({"path": str(path.relative_to(root)),
                                               "function": function, "pattern": " ".join(arm.group(2).split())})
                arms = {**arms, indent: arms.get(indent, []) + [[tree(part) for part in parts]]}
    return result
