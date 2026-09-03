(** * IDump -- the reflected IPM state dump (PLAN.md 3.1, v2 acquisition path)

    The printer-parsing path reads Iris's pretty-printed goal, which is cheap and
    layout-fragile.  This one instead matches

        envs_entails (Envs ?Γp ?Γs ?c) ?Q

    walks the two [env PROP] lists, and emits one delimited message per hypothesis.
    It is not layout-dependent, it survives Iris version bumps, and -- the reason it
    is worth the Ltac2 -- it lets printing options be set *per hypothesis*: print one
    hypothesis with [Set Printing All] while everything else stays folded.

    Each hypothesis is one [Message.print] call, and petanque returns each message as
    its own feedback entry, so the record boundaries survive transport without any
    delimiter parsing at all.

    Wire format, one message per record:

        PCP1<TAB>intuitionistic<TAB>INamed "Hinv"<TAB>inv N (I γ)
        PCP1<TAB>spatial<TAB>INamed "Hl"<TAB>l ↦ v
        PCP1<TAB>goal<TAB>-<TAB>WP e {{ Φ }}

    The prop may wrap across lines; the reader joins them. *)

From Ltac2 Require Import Ltac2.
From iris.proofmode Require Import base environments.

(** A tab-separated header keeps the reader trivial: nothing in Iris notation
    contains a tab, so the split is unambiguous even for multi-line props. *)
Ltac2 pcp_sep () := Message.of_string "	".

Ltac2 pcp_emit (klass : string) (name : message) (body : constr) :=
  Message.print
    (Message.concat (Message.of_string "PCP1	")
    (Message.concat (Message.of_string klass)
    (Message.concat (pcp_sep ())
    (Message.concat name
    (Message.concat (pcp_sep ()) (Message.of_constr body)))))).

(** Envs are snoc-lists, so the natural recursion yields them newest-first; recurse
    before emitting to report them in the order the proof mode displays them. *)
Ltac2 rec pcp_dump_env (e : constr) (klass : string) :=
  lazy_match! e with
  | Enil => ()
  | Esnoc ?rest ?i ?p =>
      pcp_dump_env rest klass;
      pcp_emit klass (Message.of_constr i) p
  | _ => Message.print (Message.concat (Message.of_string "PCP1	unknown-env	-	")
                                       (Message.of_constr e))
  end.

(** [iDump] -- dump the whole IPM state of the focused goal. *)
Ltac2 pcp_dump () :=
  lazy_match! goal with
  | [ |- envs_entails ?d ?q ] =>
      lazy_match! (Std.eval_hnf d) with
      | Envs ?gp ?gs _ =>
          pcp_dump_env gp "intuitionistic";
          pcp_dump_env gs "spatial"
      | _ => Message.print (Message.of_string "PCP1	unknown-envs	-	?")
      end;
      pcp_emit "goal" (Message.of_string "-") q
  | [ |- ?g ] =>
      (* Not an IPM goal: say so rather than emitting a half-record. *)
      pcp_emit "coq-goal" (Message.of_string "-") g
  end.

Ltac2 Notation "iDump2" := pcp_dump ().

(** Ltac1 bridges.  Proof scripts -- and the workers writing them -- are Ltac1, and
    a tool the agent has to wrap in [ltac2:(...)] at every call site is a tool it
    will get wrong.  These are the entry points pcp actually drives. *)
Ltac iDump := ltac2:(pcp_dump ()).

(** [iDumpHyp "H"] -- one hypothesis, so printing options can be set for it alone:

        Set Printing All. iDumpHyp "Hl". Unset Printing All. *)
Ltac2 rec pcp_find (e : constr) (target : constr) :=
  lazy_match! e with
  | Enil => None
  | Esnoc ?rest ?i ?p =>
      if Constr.equal i target then Some p else pcp_find rest target
  | _ => None
  end.

Ltac2 pcp_dump_hyp (n : constr) :=
  let target := constr:(INamed $n) in
  lazy_match! goal with
  | [ |- envs_entails ?d _ ] =>
      lazy_match! (Std.eval_hnf d) with
      | Envs ?gp ?gs _ =>
          match pcp_find gp target with
          | Some p => pcp_emit "intuitionistic" (Message.of_constr target) p
          | None =>
              match pcp_find gs target with
              | Some p => pcp_emit "spatial" (Message.of_constr target) p
              | None => pcp_emit "missing" (Message.of_constr target) constr:(True)
              end
          end
      | _ => Message.print (Message.of_string "PCP1	unknown-envs	-	?")
      end
  end.

Ltac2 Notation "iDumpHyp2" n(constr) := pcp_dump_hyp n.

Tactic Notation "iDumpHyp" constr(n) :=
  let f := ltac2:(n |- pcp_dump_hyp (Option.get (Ltac1.to_constr n))) in f n.
