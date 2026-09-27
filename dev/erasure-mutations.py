#!/usr/bin/env python3
"""Mutate isolated copies of the erasure increment and require named failures."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
SOURCE = "erase/opaque.bend"
KERNEL = "lib/kernel_declarations.bend"
INLINE = "erase/inline.bend"
CASES = (('proof-guard',
  'erase/opaque.bend',
  'Opaque.seal_definition(Opaque.contains(names, name), definition)',
  'Opaque.seal_definition(Bool.and(Opaque.contains(names, name), False{}), definition)',
  'OPAQUE-ERASE exit=1'),
 ('row-reinsertion',
  'erase/opaque.bend',
  'I.Inline.prepare_state(~ops, checker, F.Global.with_entries(Opaque.seal_rows(entries, names), globals), '
  'Opaque.seal_rows(rows, names))',
  'I.Inline.prepare_state(~ops, checker, F.Global.with_entries(Opaque.seal_rows(entries, names), globals), rows)',
  'OPAQUE-ERASE exit=1'),
 ('inherited-scope',
  'erase/opaque.bend',
  'I.Inline.prepare_state(~ops, checker, F.Global.with_entries(Opaque.seal_rows(entries, names), globals), '
  'Opaque.seal_rows(rows, names))',
  'I.Inline.prepare_state(~ops, checker, F.Global.with_entries(entries, globals), Opaque.seal_rows(rows, names))',
  'OPAQUE-ERASE exit=1'),
 ('inline-walker',
  'erase/opaque.bend',
  'I.Inline.prepare_state(~ops, checker, F.Global.with_entries(Opaque.seal_rows(entries, names), globals), '
  'Opaque.seal_rows(rows, names))',
  'R.Erase.Return{F.Pair2{F.Global.with_entries(Opaque.seal_rows(entries, names), globals), '
  'Opaque.seal_rows(rows, names)}}',
  'INLINE-ERASE row=let-body FAIL'),
 ('inline-name-collision',
  'erase/inline.bend',
  'Bool.or(Inline.present(F.Global.entry, F.Global.find(name, globals)), Inline.present(F.Positivity.family, '
  'F.Global.find_family(name, globals)))',
  'Bool.or(Bool.and(False{}, Inline.present(F.Global.entry, F.Global.find(name, globals))), '
  'Inline.present(F.Positivity.family, F.Global.find_family(name, globals)))',
  'INLINE-ERASE row=name-collision FAIL'),
 ('inline-local-type',
  'erase/inline.bend',
  'case F.Term.Ann{value, ty}: [F.Pair2{0n, value}, F.Pair2{0n, ty}]',
  'case F.Term.Ann{value, ty}: [F.Pair2{0n, value}]',
  'INLINE-ERASE row=local-type FAIL'),
 ('inline-row-reinsertion',
  'erase/inline.bend',
  'R.Erase.Return{here <> more}',
  'R.Erase.Return{F.Pair2{name, original} <> more}',
  'INLINE-ERASE row=rows FAIL'),
 ('inline-leg-binders',
  'erase/inline.bend',
  'F.Pair2{Inline.length(F.Pair2<F.Quantity.t, String>, binders), body}',
  'F.Pair2{0n, body}',
  'INLINE-ERASE row=binders FAIL'),
 ('inline-motive-binders',
  'erase/inline.bend',
  '[F.Pair2{1n+Inline.length(String, idx), body}]',
  '[F.Pair2{0n, body}]',
  'INLINE-ERASE row=motive FAIL'),
 ('inline-shape-payload',
  'erase/inline.bend',
  'Inline.here(F.Shape.payload(F.Term.t, s))',
  'Nil{}',
  'INLINE-ERASE row=shape-payload FAIL'),
 ('local-context',
  'erase/inline.bend',
  'next => R.Erase.Return{Some{F.Pair2{next, codomain}}}',
  'next => R.Erase.Return{Some{F.Pair2{Inline.root(next), codomain}}}',
  'INLINE-ERASE row=local-index FAIL'),
 ('local-domain-order',
  'erase/inline.bend',
  'Inline.abstract(walked, body)',
  'Inline.abstract(Inline.reverse(Inline.local, walked, Nil{}), body)',
  'INLINE-ERASE row=local-dependent FAIL'),
 ('local-argument-depth',
  'erase/inline.bend',
  'F.Term.APt{F.Quantity.Zero{}, F.Term.Var{ix}}',
  'F.Term.APt{F.Quantity.Zero{}, F.Term.Var{0n}}',
  'INLINE-ERASE row=local-dependent FAIL'),
 ('local-argument-quantity',
  'erase/inline.bend',
  'P.Rules.arrow(F.Quantity.Zero{}, name, domain, body)',
  'P.Rules.arrow(F.Quantity.One{}, name, domain, body)',
  'INLINE-ERASE row=local-dependent FAIL'),
 ('local-codomain-universe',
  'erase/inline.bend',
  'next => R.Erase.Return{Some{F.Pair2{next, codomain}}}',
  'next => Inline.mutant_codomain_state(next, codomain)',
  'INLINE-ERASE row=local-universe FAIL'),
 ('local-domain-universe',
  'erase/inline.bend',
  'P.Rules.arrow(F.Quantity.Zero{}, name, domain, body)',
  'P.Rules.arrow(F.Quantity.Zero{}, name, P.Rules.unit_ty(F.Level.zero), body)',
  'INLINE-ERASE row=local-universe FAIL'),
 ('local-branch-scope',
  'erase/inline.bend',
  'Inline.Walk{next_context, state, None{}, body, rewritten => next => done(F.Term.Leg{binders, rewritten}, next)}',
  'Inline.Walk{Inline.root(next_context), state, None{}, body, rewritten => next => done(F.Term.Leg{binders, rewritten}, next)}',
  'INLINE-ERASE row=branch-scope FAIL'),
 ('branch-field-quantity',
  'erase/inline.bend',
  'Bool.and(F.Quantity.equal(quantity, binder_quantity), Inline.closed(depth, domain))',
  'Bool.and(True{}, Inline.closed(depth, domain))',
  'INLINE-ERASE row=branch-metadata FAIL'),
 ('branch-field-depth',
  'erase/inline.bend',
  'Bool.and(F.Quantity.equal(quantity, binder_quantity), Inline.closed(depth, domain))',
  'Bool.and(F.Quantity.equal(quantity, binder_quantity), Inline.closed((depth + 1n : Nat), domain))',
  'INLINE-ERASE row=branch-metadata FAIL'),
 ('branch-field-depth-step',
  'erase/inline.bend',
  'Inline.branch_fields_valid(rest, more, (depth + 1n : Nat))',
  'Inline.branch_fields_valid(rest, more, (depth + 2n : Nat))',
  'INLINE-ERASE row=branch-metadata FAIL'),
 ('branch-ctor-name',
  'erase/inline.bend',
  'Inline.branch_ctor_state(M.Mu.ctor_of(name, value), binders, context)',
  'Inline.branch_ctor_state(Inline.mutant_head_ctor(ctors), binders, context)',
  'INLINE-ERASE row=branch-multi-ctor FAIL'),
 ('branch-ctor-last',
  'erase/inline.bend',
  'Inline.branch_ctor_state(M.Mu.ctor_of(name, value), binders, context)',
  'Inline.branch_ctor_state(Inline.mutant_last_ctor(ctors), binders, context)',
  'INLINE-ERASE row=branch-multi-ctor FAIL'),
 ('branch-param-fallback',
  'erase/inline.bend',
  '        case Con{param, rest}: R.Erase.Return{None{}}',
  '        case Con{param, rest}: Inline.branch_ctor_state(M.Mu.ctor_of(name, value), binders, context)',
  'INLINE-ERASE row=branch-fallback FAIL'),
 ('branch-missing-family',
  'erase/inline.bend',
  '    case None{}: R.Erase.Return{None{}}\n    case Some{+value}:\n      F.Positivity.Family{family_name',
  '    case None{}: R.Erase.Return{Some{context}}\n    case Some{+value}:\n      F.Positivity.Family{family_name',
  'INLINE-ERASE row=branch-fallback FAIL'),
 ('parameter-order',
  'erase/inline.bend',
  'Inline.parameter_legs(rest, body <> reversed)',
  'Inline.parameter_legs(rest, Inline.append(F.Term.t, reversed, [body]))',
  'INLINE-ERASE row=branch-parameter-dependent FAIL'),
 ('parameter-argument-shift',
  'lib/kernel_source.bend',
  'case Done{term}: Source.run(Source.Node{Source.Shift{depth}, 0n, term, done})',
  'case Done{term}: Source.run(Source.Node{Source.Shift{0n}, 0n, term, done})',
  'INLINE-ERASE row=branch-parameter-dependent FAIL'),
 ('parameter-field-depth',
  'erase/inline.bend',
  'Inline.specialize_fields(rest, arguments, (depth + 1n : Nat))',
  'Inline.specialize_fields(rest, arguments, depth)',
  'INLINE-ERASE row=branch-parameter-dependent FAIL'),
 ('parameter-arity',
  'erase/inline.bend',
  'Bool.and(Nat.is_eq(count, Inline.length(F.Term.t, args)), Bool.and(Inline.arguments_closed(args, C.Check.size(checker)), Inline.branch_fields_valid(fields, binders, count)))',
  'Bool.and(True{}, Bool.and(Inline.arguments_closed(args, C.Check.size(checker)), Inline.branch_fields_valid(fields, binders, count)))',
  'INLINE-ERASE row=branch-parameter-guards FAIL'),
 ('parameter-free-argument',
  'erase/inline.bend',
  'Bool.and(Inline.arguments_closed(args, C.Check.size(checker)), Inline.branch_fields_valid(fields, binders, count))',
  'Bool.and(True{}, Inline.branch_fields_valid(fields, binders, count))',
  'INLINE-ERASE row=branch-parameter-guards FAIL'),
 ('parameter-local-type-shift',
  'erase/inline.bend',
  'S.Source.Shift{(skipped + 1n : Nat)}, 0n, Inline.local_domain(local)',
  'S.Source.Shift{0n}, 0n, Inline.local_domain(local)',
  'INLINE-ERASE row=branch-parameter-dependent FAIL'),
 ('parameter-context-fallback',
  'erase/inline.bend',
  'Inline.parameterized_ctor_state(M.Mu.ctor_of(name, value), params, Inline.branch_arguments(ty, shape), binders, context)',
  'R.Erase.Return{None{}}',
  'INLINE-ERASE row=branch-parameter FAIL'),
 ('parameter-former-depth',
  'lib/kernel_source.bend',
  'case Some{domain}: (depth + 1n : Nat)',
  'case Some{domain}: depth',
  'INLINE-ERASE row=branch-parameter-function FAIL'),
 ('parameter-diagram-width',
  'erase/inline.bend',
  'Nat.is_eq(count, Inline.length(F.Term.leg, legs))',
  'True{}',
  'INLINE-ERASE row=branch-parameter-guards FAIL'),
 ('parameter-family-shape',
  'erase/inline.bend',
  'Inline.branch_arguments_equal(Inline.term_equal(F.Term.Lan{shape, diagram}, F.Term.Lan{source_shape, diagram}), diagram)',
  'Inline.parameter_diagram(diagram)',
  'INLINE-ERASE row=branch-parameter-guards FAIL'),
 # Two constructors share one field shape. The suite row seals a proof in
 # the first constructor and a proof in the last constructor.
 ('parameter-ctor-name',
  'erase/inline.bend',
  'Inline.parameterized_ctor_state(M.Mu.ctor_of(name, value), params,',
  'Inline.parameterized_ctor_state(Inline.mutant_head_ctor(ctors), params,',
  'INLINE-ERASE row=branch-parameter-ctor FAIL'),
 ('parameter-ctor-last',
  'erase/inline.bend',
  'Inline.parameterized_ctor_state(M.Mu.ctor_of(name, value), params,',
  'Inline.parameterized_ctor_state(Inline.mutant_last_ctor(ctors), params,',
  'INLINE-ERASE row=branch-parameter-ctor FAIL'),
 # Field specialization must keep universes and annotations as source syntax.
 ('parameter-field-quote',
  'erase/inline.bend',
  ('arguments: List<&2, F.Term.t>, binders: List<&2, F.Pair2<F.Quantity.t, String>>, context: Inline.context) -> '
   'R.Erase.State<Maybe<&2, Inline.context>>:\n  match valid:',
   'R.Erase.State.lift(F.Positivity.telescope, Inline.specialize_fields(fields, arguments, 0n)), specialized =>'),
  ('arguments: List<&2, F.Term.t>, binders: List<&2, F.Pair2<F.Quantity.t, String>>, +context: Inline.context) -> '
   'R.Erase.State<Maybe<&2, Inline.context>>:\n  match valid:',
   'R.Erase.State.lift(F.Positivity.telescope, Inline.mutant_quote_fields(Inline.specialize_fields(fields, arguments, 0n), '
   'context)), specialized =>'),
  'INLINE-ERASE row=branch-parameter-universe FAIL'),
 ('parameter-source-universe',
  'lib/kernel_source.bend',
  '        case other: done(other)\n\ndef Source.term(',
  '        case F.Term.Univ{level}: done(F.Term.Univ{F.Level.succ(level)})\n        case other: done(other)\n\n'
  'def Source.term(',
  'INLINE-ERASE row=branch-parameter-universe FAIL'),
 ('quote-elimination-environment',
  'lib/kernel_eval.bend',
  'Eval.quote_task(Eval.QuoteMotive{motive, env, size, mo =>\n'
  '                  Eval.quote_task(Eval.QuoteBranches{branches, env, size, bs =>\n'
  '                    Eval.quote_task(Eval.QuoteFrames{rest, F.Term.Elim{F.Term.Elimination{s, head, q, mo, bs}}, size, done}, globals)}, globals)}, globals)',
  'Eval.quote_task(Eval.QuoteFrames{rest, F.Term.Elim{F.Term.Elimination{s, head, q, motive, branches}}, size, done}, globals)',
  'INLINE-ERASE row=branch-parameter FAIL'),
 # The kernel unit case quotes a stuck elimination whose motive reads an
 # outer binder. These two probes break only the motive half of quote.
 ('quote-elimination-motive',
  'lib/kernel_eval.bend',
  ('F.Value.StuckElim{shape, q, motive, branches, +env} = elimination',
   'F.Term.Elim{F.Term.Elimination{s, head, q, mo, bs}}'),
  ('F.Value.StuckElim{shape, q, +motive, branches, +env} = elimination',
   'F.Term.Elim{F.Term.Elimination{s, head, q, motive, bs}}'),
  'FAIL kernel case 17'),
 ('quote-motive-binders',
  'lib/kernel_eval.bend',
  'Eval.QuoteOpen{env, (1n + List.length(&2, String, indices) : Nat), body, size, b =>',
  'Eval.QuoteOpen{env, List.length(&2, String, indices), body, size, b =>',
  'FAIL kernel case 17'),
 ('leg-scope-root',
  'erase/inline.bend',
  '    case other: Inline.root(context)\n\n# Constructor types',
  '    case other: context\n\n# Constructor types',
  'INLINE-ERASE row=alias-leg-scope FAIL'),
 ('local-inferred-universe',
  'erase/inline.bend',
  'Inline.infer_closed_state(~ops, Inline.closed(0n, other), checker, other)',
  'Inline.infer_closed_state(~ops, Inline.closed(C.Check.size(checker), other), checker, other)',
  'INLINE-ERASE row=local-runtime-call FAIL'),
 ('local-proof-let',
  'erase/inline.bend',
  'Bool.and(Inline.closed(C.Check.size(checker), domain), Inline.typed(0n, body))',
  'Bool.and(Bool.and(Inline.closed(C.Check.size(checker), domain), Inline.typed(0n, body)), False{})',
  'INLINE-ERASE row=local-proof-let FAIL'),
 ('local-proof-let-value',
  'erase/inline.bend',
  '        case True{}:\n'
  '          Inline.run_state(~ops, Inline.Walk{context, state, None{}, domain, rewritten => next =>\n'
  '            Inline.bind_state(Inline.context, F.Pair2<F.Term.t, Inline.state>, '
  'Inline.define_let_state(context, name, domain, value), scope =>\n'
  '              Inline.run_state(~ops, Inline.Domains{locals, scope, next, Inline.Local{name, rewritten, '
  'value} <> walked, ty, done}))})\n',
  '        case True{}:\n'
  '          Inline.run_state(~ops, Inline.Walk{context, state, Some{domain}, value, sealed => next =>\n'
  '            Inline.run_state(~ops, Inline.Walk{context, next, None{}, domain, rewritten => after =>\n'
  '              Inline.bind_state(Inline.context, F.Pair2<F.Term.t, Inline.state>, '
  'Inline.define_let_state(context, name, domain, value), scope =>\n'
  '                Inline.run_state(~ops, Inline.Domains{locals, scope, after, Inline.Local{name, rewritten, '
  'sealed} <> walked, ty, done}))})})\n',
  'INLINE-ERASE row=local-proof-let-value FAIL'),
 ('local-proof-let-type',
  'erase/inline.bend',
  'case F.Term.Let{name, ty, value, body}: Bool.or(Inline.occurs(target, ty), Inline.occurs(target, value))',
  'case F.Term.Let{name, ty, value, body}: Bool.or(Inline.occurs(target, ty), Bool.and(Inline.occurs(target, '
  'value), False{}))',
  'INLINE-ERASE row=local-proof-let-type FAIL'),
 ('local-proof-let-alias',
  'erase/inline.bend',
  'case F.Term.Let{name, ty, value, body}: Bool.or(Inline.occurs(target, ty), Inline.occurs(target, value))',
  'case F.Term.Let{name, +ty, value, body}: Bool.or(Inline.occurs(target, ty), '
  'Bool.and(Inline.mutant_universe(ty), Inline.occurs(target, value)))',
  'INLINE-ERASE row=local-proof-let-alias FAIL'),
 ('inline-twin-extra-edit',
  'fixtures/erasure/local-let-opaque.att',
  '| refl : (0 n : Nat) -> Equal n',
  '| refl : (0 m : Nat) -> Equal m',
  'row=local-let opaque twin changes more than its proof'),
 ('inline-twin-same-line-edit',
  'fixtures/erasure/local-let-opaque.att',
  'case proof n as p in Equal k',
  'case proof n as r in Equal k',
  'row=local-let opaque twin changes more than its proof'),
 ('inline-twin-adjacent-let-drop',
  'fixtures/erasure/let-proof.att',
  ':= refl in case p',
  ':= refl in let u : Type 0 := Nat in case p',
  'row=let-proof opaque twin changes more than its proof'),
 ('inline-twin-repeated-arg',
  'fixtures/erasure/branch-nested-opaque.att',
  'case proof outer n m as p',
  'case proof outer outer n as p',
  'row=branch-nested opaque twin changes more than its proof'),
 ('missing-twin', 'fixtures/erasure/f2-a-opaque.att', None, None, 'row=f2-a opaque twin missing'),
 ('lean-sorry',
  'twin/F2.lean',
  'def proof : AttestTwin.Equal := .refl trivial',
  'def proof : AttestTwin.Equal := sorry',
  'LEAN-F2 exit=1 expected=0'),
 ('prop-index-withdrawn',
  'lib/kernel_declarations.bend',
  'Bool.or(F.Level.equal(level, F.Level.zero), F.Level.le(inferred, level))',
  'F.Level.le(inferred, level)',
  'PROP-INDEX row=nat-index FAIL'),
 ('type-index-unbounded',
  'lib/kernel_declarations.bend',
  'Bool.or(F.Level.equal(level, F.Level.zero), F.Level.le(inferred, level))',
  'F.Level.le(inferred, inferred)',
  'PROP-INDEX row=type-index-bound FAIL'),
 ('prop-field-quantity',
  'lib/kernel_declarations.bend',
  'Bool.and(F.Quantity.equal(q, F.Quantity.Zero{}), Check.any_parameter(Nat.sub(depth, 1n), indices))',
  'Bool.and(Bool.or(F.Quantity.equal(q, F.Quantity.Zero{}), True{}), Check.any_parameter(Nat.sub(depth, 1n), '
  'indices))',
  'PROP-INDEX row=runtime-proof-field FAIL'),
 ('prop-field-unindexed',
  'lib/kernel_declarations.bend',
  'Check.any_parameter(Nat.sub(depth, 1n), indices)',
  'Bool.or(Check.any_parameter(Nat.sub(depth, 1n), indices), True{})',
  'PROP-INDEX row=unindexed-proof-field FAIL'),
 ('prop-field-depth',
  'lib/kernel_declarations.bend',
  ('+depth: Nat) -> S.Kernel.Program<C.Check.ctx>:',
   'Check.any_parameter(Nat.sub(depth, 1n), indices)',
   'Check.check_fields(rest, next, level, name, indices, Nat.sub(depth, 1n))',
   'Check.check_fields(args, ctx, level, name, result_indices, depth)'),
  ('+depth: Nat, +index: Nat) -> S.Kernel.Program<C.Check.ctx>:',
   'Check.any_parameter(index, indices)',
   'Check.check_fields(rest, next, level, name, indices, Nat.sub(depth, 1n), Nat.add(index, 1n))',
   'Check.check_fields(args, ctx, level, name, result_indices, depth, 0n)'),
  'PROP-INDEX row=accessibility-family FAIL'))


CODOMAIN_MUTANT = '\n\ndef Inline.mutant_codomain_state(+context: Inline.context, codomain: F.Term.t) -> R.Erase.State<Maybe<&2, F.Pair2<Inline.context, F.Term.t>>>:\n  Inline.Context{+checker, domains} = context\n  do R.Erase.State<Maybe<&2, F.Pair2<Inline.context, F.Term.t>>>:\n    value: F.Value.t <- R.Erase.State.lift(F.Value.t, E.Eval.eval(C.Check.global(checker), C.Check.environment(checker), codomain))\n    quoted: F.Term.t <- R.Erase.State.lift(F.Term.t, E.Eval.quote(C.Check.global(checker), C.Check.size(checker), value))\n    R.Erase.Return{Some{F.Pair2{context, quoted}}}\n'

QUOTE_FIELDS_MUTANT = (
    "def Inline.mutant_quote_telescope(fields: F.Positivity.telescope, +context: Inline.context) "
    "-> Result<&2,&2,F.Error.t,F.Positivity.telescope>:\n"
    "  match fields:\n    case Nil{}: Done{Nil{}}\n"
    "    case F.Triple3{quantity, name, domain} <> rest:\n"
    "      Inline.Context{+checker, domains} = context\n"
    "      do Result<&2,&2,F.Error.t,F.Positivity.telescope>:\n"
    "        value: F.Value.t <- E.Eval.eval(C.Check.global(checker), C.Check.environment(checker), domain)\n"
    "        ty: F.Term.t <- E.Eval.quote(C.Check.global(checker), C.Check.size(checker), value)\n"
    "        Done{F.Triple3{quantity, name, ty} <> rest}\n\n"
    "def Inline.mutant_quote_fields(fields: Result<&2,&2,F.Error.t,F.Positivity.telescope>, +context: Inline.context) "
    "-> Result<&2,&2,F.Error.t,F.Positivity.telescope>:\n"
    "  match fields:\n    case Fail{error}: Fail{error}\n"
    "    case Done{telescope}: Inline.mutant_quote_telescope(telescope, context)\n\n")

CASES += (
    ("motive-root-context", INLINE,
     "Inline.Walk{Inline.motive_scope(scope, context), state, None{}, body,",
     "Inline.Walk{Inline.root(context), state, None{}, body,",
     "INLINE-ERASE row=motive-index FAIL"),
    ("motive-self-indices", INLINE,
     "F.Shape.make_inductive(F.Term.t, ind, Inline.motive_variables(count))",
     "F.Shape.make_inductive(F.Term.t, ind, Inline.motive_variables(0n))",
     "INLINE-ERASE row=motive-index FAIL"),
    ("motive-index-order", INLINE,
     "F.Term.Var{index} <> Inline.motive_variables(index)",
     "F.Term.Var{0n} <> Inline.motive_variables(index)",
     "INLINE-ERASE row=motive-dependent FAIL"),
    ("motive-parameter-shift", INLINE,
     "S.Source.Shift{count}, 0n, P.Rules.diagram_of(",
     "S.Source.Shift{0n}, 0n, P.Rules.diagram_of(",
     "INLINE-ERASE row=motive-parameter FAIL"),
    ("motive-parameter-shift-constant", INLINE,
     "S.Source.Shift{count}, 0n, P.Rules.diagram_of(",
     "S.Source.Shift{1n}, 0n, P.Rules.diagram_of(",
     "INLINE-ERASE row=motive-parameter-indices FAIL"),
    ("motive-parameter-substitution", INLINE,
     "specialized: F.Positivity.telescope <- R.Erase.State.lift(F.Positivity.telescope, Inline.specialize_fields(fields, arguments, 0n))",
     "specialized: F.Positivity.telescope <- R.Erase.State.lift(F.Positivity.telescope, Inline.specialize_fields(fields, Nil{}, 0n))",
     "INLINE-ERASE row=motive-parameter FAIL"),
    ("motive-field-scope", INLINE,
     "Bool.and(Inline.closed(depth, domain), Inline.motive_fields_valid(rest, more, (depth + 1n : Nat)))",
     "Bool.and(True{}, Inline.motive_fields_valid(rest, more, (depth + 1n : Nat)))",
     "INLINE-ERASE row=motive-guards FAIL"),
    ("motive-index-quantity", INLINE,
     "Inline.bind_domain_state(context, name, F.Quantity.Zero{}, domain), scope =>\n        Inline.motive_fields_state",
     "Inline.bind_domain_state(context, name, F.Quantity.One{}, domain), scope =>\n        Inline.motive_fields_state",
     "INLINE-ERASE row=motive-quantities FAIL"),
    ("motive-self-quantity", INLINE,
     "Inline.bind_domain_state(context, self, F.Quantity.Zero{}, self_ty)",
     "Inline.bind_domain_state(context, self, F.Quantity.One{}, self_ty)",
     "INLINE-ERASE row=motive-quantities FAIL"),
    ("motive-family-match", INLINE,
     "Bool.and(String.eq(ind, family), Nat.is_eq(Inline.length(F.Term.t, indices), Inline.length(String, names)))",
     "Bool.and(True{}, Nat.is_eq(Inline.length(F.Term.t, indices), Inline.length(String, names)))",
     "INLINE-ERASE row=motive-guards FAIL"),
    ("motive-shape-count", INLINE,
     "Nat.is_eq(Inline.length(F.Term.t, indices), Inline.length(String, names))",
     "True{}",
     "INLINE-ERASE row=motive-guards FAIL"),
    ("motive-parameter-count", INLINE,
     "Bool.and(Nat.is_eq(count, Inline.length(F.Term.t, args)), Bool.and(Inline.arguments_closed(args, C.Check.size(checker)), Inline.motive_fields_valid(fields, names, count)))",
     "Bool.and(True{}, Bool.and(Inline.arguments_closed(args, C.Check.size(checker)), Inline.motive_fields_valid(fields, names, count)))",
     "INLINE-ERASE row=motive-guards FAIL"),
    ("motive-free-argument", INLINE,
     "Bool.and(Inline.arguments_closed(args, C.Check.size(checker)), Inline.motive_fields_valid(fields, names, count))",
     "Bool.and(True{}, Inline.motive_fields_valid(fields, names, count))",
     "INLINE-ERASE row=motive-guards FAIL"),
    ("motive-field-depth", INLINE,
     "Inline.motive_fields_valid(rest, more, (depth + 1n : Nat))",
     "Inline.motive_fields_valid(rest, more, (depth + 2n : Nat))",
     "INLINE-ERASE row=motive-guards FAIL"),
    ("plain-motive-disabled", INLINE,
     "case None{}: Inline.motive_plain_view_state(F.Shape.inductive(F.Term.t, shape), scrut, names, self, context)",
     "case None{}: R.Erase.Return{None{}}",
     "INLINE-ERASE row=motive-plain-local FAIL"),
    ("plain-motive-self-quantity", INLINE,
     "Inline.bind_domain_state(context, self, F.Quantity.Zero{}, domain)",
     "Inline.bind_domain_state(context, self, F.Quantity.One{}, domain)",
     "INLINE-ERASE row=motive-plain-quantity FAIL"),
    # Inline.bind_domain_state repeats the closure check of
    # Inline.source_expected, so this case removes both checks.
    ("plain-motive-free-type", INLINE,
     ("Inline.motive_plain_type_state(Inline.source_expected(ty, C.Check.size(checker)), self, context)",
      "Inline.bind_domain_state(context, self, F.Quantity.Zero{}, domain)"),
     ("Inline.motive_plain_type_state(ty, self, context)",
      "Inline.bind_closed_state(True{}, context, self, F.Quantity.Zero{}, domain)"),
     "INLINE-ERASE row=motive-plain-guards FAIL mismatch: plain motive free annotation acquired a context"),
    ("plain-motive-indices", INLINE,
     "case head <> tail: R.Erase.Return{None{}}\n    case Nil{}:\n      Inline.Context{checker, domains} = context",
     'case head <> tail: Inline.motive_plain_type_state(Some{F.Term.Global{"Nat"}}, self, context)\n    case Nil{}:\n      Inline.Context{checker, domains} = context',
     "INLINE-ERASE row=motive-plain-guards FAIL mismatch: plain motive index names acquired a context"),
    ("plain-motive-family", INLINE,
     "case Some{family}: R.Erase.Return{None{}}\n    case None{}: Inline.motive_plain_names_state(names, scrut, self, context)",
     "case Some{family}: Inline.motive_plain_names_state(names, scrut, self, context)\n    case None{}: Inline.motive_plain_names_state(names, scrut, self, context)",
     "INLINE-ERASE row=motive-plain-guards FAIL mismatch: plain motive inductive shape acquired a context"),
    # The quantity row annotates the scrutinee with a type other than Nat,
    # so a hardcoded Nat self domain must fail it.
    ("plain-motive-self-domain", INLINE,
     "Inline.bind_domain_state(context, self, F.Quantity.Zero{}, domain)",
     'Inline.bind_domain_state(context, self, F.Quantity.Zero{}, F.Term.Global{"Nat"})',
     "INLINE-ERASE row=motive-plain-quantity FAIL"),
    # The checker entry gets a different type while the Inline parameter
    # keeps the source domain; the quantity row quotes the checker entry.
    ("plain-motive-checker-type", INLINE,
     "C.Check.environment(checker), domain)), value =>\n        R.Erase.Return{Inline.Context{C.Check.bind(name, quantity, value, checker), Inline.Param{name, domain} <> domains}})",
     'C.Check.environment(checker), F.Term.Global{"Nat"})), value =>\n        R.Erase.Return{Inline.Context{C.Check.bind(name, quantity, value, checker), Inline.Param{name, domain} <> domains}})',
     "INLINE-ERASE row=motive-plain-quantity FAIL"),
    ("plain-motive-unknown-term", INLINE,
     "        Inline.application_source_type(ty, address, context)\n    case other: Done{None{}}",
     '        Inline.application_source_type(ty, address, context)\n    case other: Done{Some{F.Term.Global{"Nat"}}}',
     "INLINE-ERASE row=motive-plain-guards FAIL mismatch: plain motive unavailable source type acquired a context"),
    ("application-disabled", INLINE,
     "Inline.application_type(expanded, address, C.Check.size(checker))",
     "Done{None{}}",
     "INLINE-ERASE row=motive-application-global FAIL"),
    ("application-outer-shift", INLINE,
     "argument <> Inline.source_variables(depth, 0n)",
     "argument <> Inline.source_variables(depth, 1n)",
     "INLINE-ERASE row=application-capture FAIL"),
    ("application-free-codomain", INLINE,
     "Inline.closed((depth + 1n : Nat), codomain), Inline.closed(depth, argument)",
     "True{}, Inline.closed(depth, argument)",
     "INLINE-ERASE row=application-guards FAIL mismatch: parameter outside its telescope"),
    ("application-free-argument", INLINE,
     "Inline.closed((depth + 1n : Nat), codomain), Inline.closed(depth, argument)",
     "Inline.closed((depth + 1n : Nat), codomain), True{}",
     "INLINE-ERASE row=application-guards FAIL mismatch: application free argument accepted"),
    ("application-nonpoint", INLINE,
     "case None{}: Done{None{}}\n    case Some{F.Triple3{q, name, domain}}:",
     'case None{}: Done{Some{F.Term.Global{"Nat"}}}\n    case Some{F.Triple3{q, name, domain}}:',
     "INLINE-ERASE row=application-guards FAIL mismatch: application nonpoint former accepted"),
    ("alias-disabled", INLINE,
     "Inline.alias_type((aliases + 1n : Nat), ty, context)",
     "Done{ty}",
     "INLINE-ERASE row=motive-alias-global FAIL"),
    ("alias-global-scope", INLINE,
     "Inline.source_expected(Some{body}, 0n)",
     "Some{body}",
     "INLINE-ERASE row=alias-guards FAIL mismatch: free global alias accepted"),
    ("alias-local-scope", INLINE,
     "Inline.shift_alias(Inline.closed(Inline.length(Inline.local, rest), value), value, skipped)",
     "Inline.shift_alias(True{}, value, skipped)",
     "INLINE-ERASE row=alias-guards FAIL mismatch: self-referencing local alias accepted"),
    ("alias-local-shift", INLINE,
     "S.Source.term(S.Source.Shift{(skipped + 1n : Nat)}, 0n, value)",
     "S.Source.term(S.Source.Shift{skipped}, 0n, value)",
     "INLINE-ERASE row=alias-local FAIL"),
    ("alias-opaque", INLINE,
     "F.Global.DefEntry{ty, body, True{}, None{}, False{}}",
     "F.Global.DefEntry{ty, body, reducible, None{}, False{}}",
     "INLINE-ERASE row=alias-guards FAIL mismatch: opaque alias unfolded"),
    ("alias-recursive", INLINE,
     "F.Global.DefEntry{ty, body, True{}, None{}, False{}}",
     "F.Global.DefEntry{ty, body, True{}, recursive, False{}}",
     "INLINE-ERASE row=alias-guards FAIL mismatch: recursive alias unfolded"),
    ("alias-partial", INLINE,
     "F.Global.DefEntry{ty, body, True{}, None{}, False{}}",
     "F.Global.DefEntry{ty, body, True{}, None{}, partial}",
     "INLINE-ERASE row=alias-guards FAIL mismatch: partial alias unfolded"),
    ("alias-fuel-bound", INLINE,
     "Inline.alias_type((aliases + 1n : Nat), ty, context)",
     "Inline.alias_type(3n, ty, context)",
     "INLINE-ERASE row=alias-fuel FAIL mismatch: application source type missing"),
    ("alias-fuel-plus-one", INLINE,
     "Inline.alias_type((aliases + 1n : Nat), ty, context)",
     "Inline.alias_type(aliases, ty, context)",
     "INLINE-ERASE row=alias-fuel FAIL mismatch: application source type missing"),
    ("alias-fuel-zero", INLINE,
     "case 0n ty: Done{None{}}",
     "case 0n ty: Done{ty}",
     "INLINE-ERASE row=alias-fuel FAIL mismatch: exhausted alias fuel accepted"),
    ("alias-local-global", INLINE,
     "Inline.alias_type(remaining, body, context)",
     "Inline.alias_type(remaining, body, Inline.Context{C.Check.make(F.Global.empty, C.Check.budget(checker)), domains})",
     "INLINE-ERASE row=alias-local-global FAIL mismatch: application source type missing"),
    ("plain-motive-fixture-binding", "erase/test/inline_test.bend",
     "MF.Fixture.motive_plain_local,MF.Fixture.motive_plain_local_opaque",
     "MF.Fixture.motive_plain_global,MF.Fixture.motive_plain_global_opaque",
     "row=motive-plain-local motive fixture call differs"),
    ("motive-fixture-binding", "erase/test/inline_test.bend",
     "MF.Fixture.motive_index,MF.Fixture.motive_index_opaque",
     "MF.Fixture.motive_self,MF.Fixture.motive_self_opaque",
     "row=motive-index motive fixture call differs"),
    ("parameter-fixture-binding", "erase/test/inline_test.bend",
     "PF.Fixture.branch_parameter_global,PF.Fixture.branch_parameter_global_opaque",
     "PF.Fixture.branch_parameter,PF.Fixture.branch_parameter_opaque",
     "row=branch-parameter-global parameter fixture call differs"),
    # The correct motive-index line stays in an unused definition while the
    # live case calls another valid pair.
    ("fixture-binding-dead-copy", "erase/test/inline_test.bend",
     ("MF.Fixture.motive_index,MF.Fixture.motive_index_opaque", "def Suite.cases("),
     ("MF.Fixture.motive_self,MF.Fixture.motive_self_opaque",
      "def Suite.mutant_dead_cases() -> List<Suite.case>:\n  [\n"
      "      Suite.Case{\"motive-index\",unit => Suite.local_sealed(MF.Fixture.motive_index,"
      "MF.Fixture.motive_index_opaque,None{},1n)} ]\n\ndef Suite.cases("),
     "row=motive-index motive fixture call differs"),
)


def mutate_source(name, source, before, after):
    edits = zip(before, after) if isinstance(before, tuple) else [(before, after)]
    for old, new in edits:
        if source.count(old) != 1:
            raise ValueError(f"{name}: mutation anchor is not unique: {old!r}")
        source = source.replace(old, new, 1)
    if name == "local-codomain-universe":
        source = source.replace("def Inline.lambda_bind_state(", CODOMAIN_MUTANT + "\ndef Inline.lambda_bind_state(", 1)
    if name == "local-inferred-universe":
        source = source.replace("def Inline.infer_source_state(~ops: Inline.Semantics, term: F.Term.t, checker:",
                                "def Inline.infer_source_state(~ops: Inline.Semantics, term: F.Term.t, +checker:", 1)
    if name == "local-proof-let-alias":
        helper = "def Inline.mutant_universe(term: F.Term.t) -> Bool:\n  match term:\n    case F.Term.Univ{level}: True{}\n    case other: False{}\n\n"
        source = source.replace("def Inline.typed_here(", helper + "def Inline.typed_here(", 1)
    if name in ("branch-ctor-name", "parameter-ctor-name"):
        helper = ("def Inline.mutant_head_ctor(ctors: List<&2, F.Positivity.ctor>) -> Maybe<&2, F.Positivity.ctor>:\n"
                  "  match ctors:\n    case Nil{}: None{}\n    case Con{ctor, rest}: Some{ctor}\n\n")
        source = source.replace("def Inline.branch_family_state(", helper + "def Inline.branch_family_state(", 1)
    if name in ("branch-ctor-last", "parameter-ctor-last"):
        helper = ("def Inline.mutant_last_ctor(ctors: List<&2, F.Positivity.ctor>) -> Maybe<&2, F.Positivity.ctor>:\n"
                  "  match ctors:\n    case Nil{}: None{}\n    case Con{ctor, more}:\n"
                  "      match more:\n        case Nil{}: Some{ctor}\n        case Con{next, tail}: Inline.mutant_last_ctor(more)\n\n")
        source = source.replace("def Inline.branch_family_state(", helper + "def Inline.branch_family_state(", 1)
    if name == "parameter-field-quote":
        source = source.replace("def Inline.specialized_branch_state(", QUOTE_FIELDS_MUTANT + "def Inline.specialized_branch_state(", 1)
    return source


def digest(data):
    return hashlib.sha256(data).hexdigest()


def run(root, command):
    environment = dict(os.environ)
    environment.setdefault("ATTEST_BEND_ROOT", str(ROOT / "_tools/bend"))
    return subprocess.run(command, cwd=root, env=environment, capture_output=True, timeout=900)


def run_case(case, logs, scratch_root, snapshot):
    name, relative, before, after, diagnostic = case
    with tempfile.TemporaryDirectory(dir=scratch_root, prefix=name + "-") as directory:
        scratch = Path(directory) / "tree"
        shutil.copytree(snapshot, scratch, ignore=shutil.ignore_patterns(
            ".git", "_build", "_tools", ".lake", ".gatework", ".kanon-*", "__pycache__"))
        # Copy only JS artifacts; build.py verifies source and output hashes
        # before reuse and recompiles every affected dependency graph.
        cached = snapshot / "_build/js"
        if cached.is_dir():
            shutil.copytree(cached, scratch / "_build/js")
        path = scratch / relative
        original = path.read_bytes()
        if before is None:
            path.unlink()
            changed = None
        else:
            source = original.decode()
            changed = mutate_source(name, source, before, after).encode()
            path.write_bytes(changed)
        # A kernel unit probe also builds and runs test/kernel.bend directly.
        kernel = diagnostic.startswith("FAIL kernel case ")
        build_command = ["python3", "-P", "dev/build.py", "--backend", "js",
                         "attest", "erase-probe", "prop-index", "opaque", "inline"] + (["kernel"] if kernel else [])
        build = run(scratch, build_command)
        (logs / (name + "-build.log")).write_bytes(build.stdout + build.stderr)
        if build.returncode:
            raise ValueError(f"{name}: build failed, not a caught behavior mutation")
        gate_command = ["python3", "-P", "dev/erasure-gates.py"]
        result = run(scratch, gate_command)
        output = result.stdout + result.stderr
        (logs / (name + ".log")).write_bytes(
            output.replace(str(scratch).encode(), b"<mutation-tree>"))
        if diagnostic.startswith("PROP-INDEX row="):
            if b"PROP-INDEX exit=1 expected=0" not in output:
                raise ValueError(f"{name}: did not reach the Prop index regression")
            output += (scratch / ".gatework/erasure/PROP-INDEX.log").read_bytes()
        if diagnostic.startswith("INLINE-ERASE row="):
            if b"INLINE-ERASE exit=1 expected=0" in output:
                output += (scratch / ".gatework/erasure/INLINE-ERASE.log").read_bytes()
            else:
                # An earlier gate can fail on the same fault. Also require
                # the named semantic regression in the compiled mutant.
                unit = run(scratch, ["_build/default/erase/test/inline_test.exe"])
                output += b"\nINLINE-ERASE direct regression:\n" + unit.stdout + unit.stderr
                (logs / (name + ".log")).write_bytes(
                    output.replace(str(scratch).encode(), b"<mutation-tree>"))
                if unit.returncode != 1:
                    raise ValueError(f"{name}: inline proof regression exit={unit.returncode}")
        unit_command = ["_build/default/test/kernel.exe"]
        unit = run(scratch, unit_command) if kernel else None
        if kernel:
            output += b"\nKERNEL direct regression:\n" + unit.stdout + unit.stderr
        judged = unit.returncode if kernel else result.returncode
        # A temporary checkout path is not part of a diagnostic's identity.
        output = output.replace(str(scratch).encode(), b"<mutation-tree>")
        (logs / (name + ".log")).write_bytes(output)
        if judged != 1 or diagnostic.encode() not in output:
            raise ValueError(f"{name}: expected named gate failure {diagnostic!r}")
        return {"name": name, "path": relative, "before_sha256": digest(original),
            "mutated_sha256": None if changed is None else digest(changed),
            "log_sha256": digest(output),
            "build_exit": build.returncode, "gate_exit": result.returncode,
            "diagnostic": diagnostic, "build_command": build_command, "gate_command": gate_command,
            **({"unit_command": unit_command, "unit_exit": unit.returncode} if kernel else {}),
            **({"deleted": True} if changed is None else {})}


def run_cases(cases, logs, scratch_root, snapshot, jobs):
    # Each worker owns its checkout and case-named logs. Only the immutable
    # source snapshot and pinned toolchain are shared. Collect in catalog order.
    if jobs not in (1, 2):
        raise ValueError("mutation concurrency must be 1 or 2")
    if len({case[0] for case in cases}) != len(cases):
        raise ValueError("mutation case names must be unique for isolated logs")
    pool = ThreadPoolExecutor(max_workers=jobs)
    try:
        futures = [pool.submit(run_case, case, logs, scratch_root, snapshot) for case in cases]
        records = []
        for future in futures:
            record = future.result()
            records.append(record)
            print(f"ERASURE-MUTATION {record['name']} caught", flush=True)
        return records
    finally:
        # A failed case remains a failed battery. Cancel queued work and wait
        # for at most the other running worker to finish its isolated cleanup.
        pool.shutdown(wait=True, cancel_futures=True)


def implementation_hashes(root):
    sources = {"dev/erasure-mutations.py", "dev/erasure-gates.py", "dev/build.py",
               "dev/bend-toolchain.json", "dev/bend-migration.json", "dev/cc.py",
               "dev/erase_probe.bend", "Makefile"}
    sources.update(str(path.relative_to(root)) for folder in ("lib", "surface", "erase", "bin")
                   for path in (root / folder).rglob("*.bend"))
    return {path: digest((root / path).read_bytes()) for path in sorted(sources)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    parser.add_argument("--jobs", type=int, choices=(1, 2), default=1,
                        help="independent isolated cases to run concurrently (maximum 2)")
    parser.add_argument("--case", action="append", choices=[case[0] for case in CASES],
                        help="run named cases; partial runs cannot produce release records")
    parser.add_argument("--check-anchors", action="store_true",
                        help="validate all source anchors without building or running gates")
    args = parser.parse_args()
    if args.record and (args.case or args.check_anchors):
        parser.error("--record requires the complete mutation battery")
    logs = ROOT / ("dev/validation/erasure-mutations" if args.record else ".gatework/erasure-mutations")
    logs.mkdir(parents=True, exist_ok=True)
    scratch_root = ROOT / ".gatework/erasure-copies"
    scratch_root.mkdir(parents=True, exist_ok=True)
    try:
        if args.check_anchors:
            for name, relative, before, after, diagnostic in CASES:
                source = (ROOT / relative).read_text()
                if before is not None and mutate_source(name, source, before, after) == source:
                    raise ValueError(f"{name}: mutation made no change")
            print(f"ERASURE-MUTATION-ANCHORS checked={len(CASES)} OK")
            return 0
        inputs = implementation_hashes(ROOT)
        baseline = run(ROOT, ["python3", "-P", "dev/erasure-gates.py"])
        (logs / "baseline.log").write_bytes(baseline.stdout + baseline.stderr)
        if baseline.returncode != 0:
            raise ValueError("unmutated erasure gate failed")
        records = []
        selected = [case for case in CASES if args.case is None or case[0] in args.case]
        with tempfile.TemporaryDirectory(dir=ROOT / ".gatework", prefix="erasure-input-") as directory:
            snapshot = Path(directory) / "tree"
            # Freeze inputs before launching workers so no worker copies another
            # worker's changing logs or artifacts from the shared checkout.
            shutil.copytree(ROOT, snapshot, ignore=shutil.ignore_patterns(
                ".git", "_build", "_tools", ".lake", ".gatework", ".kanon-*", "__pycache__"))
            if (ROOT / "_build/js").is_dir():
                shutil.copytree(ROOT / "_build/js", snapshot / "_build/js")
            if implementation_hashes(snapshot) != inputs:
                raise ValueError("implementation changed during the baseline or input snapshot")
            records = run_cases(selected, logs, scratch_root, snapshot, args.jobs)
        if implementation_hashes(ROOT) != inputs:
            raise ValueError("implementation changed during the mutation battery")
        if args.record:
            record = {"version": 1, "jobs": args.jobs, "baseline_sha256": digest(baseline.stdout + baseline.stderr),
                      "implementation_sha256": inputs,
                      "mutations": records}
            (ROOT / "dev/validation/erasure-mutations.json").write_text(json.dumps(record, indent=2) + "\n")
        suffix = " OK" if len(selected) == len(CASES) else " PARTIAL"
        print(f"ERASURE-MUTATIONS caught={len(records)} total={len(CASES)}" + suffix)
        return 0
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"ERASURE-MUTATIONS FAIL: {error}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
