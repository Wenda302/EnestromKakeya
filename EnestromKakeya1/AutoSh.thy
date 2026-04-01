theory AutoSh
imports Main
begin

ML \<open>

(* sh: a proof method that runs sledgehammer and succeeds iff a proof is found.
   Works in both interactive (jedit) and batch (isabelle build) mode.

   On success, ONE line is appended to /tmp/isabelle_sh_results.txt:
       <file>:<line> | <goal (first 80 chars)> | <by tactic>

   Workflow (use at most ONE `by sh` per build to avoid ATP conflicts):
     1. Replace one `sorry` with `by sh`
     2. rm -f /tmp/isabelle_sh_results.txt && isabelle build -D .
     3. Read the recorded tactic from /tmp/isabelle_sh_results.txt
     4. Replace `by sh` with the recorded tactic in the source

   Proving power: uses one ATP prover (same as sledgehammer_with_metis_tac)
   and tries metis → simp → auto in order, recording whichever succeeds.
   This is slightly weaker than interactive `sledgehammer` which runs multiple
   provers in parallel; re-run if the first attempt fails. *)

fun sh_record line =
  let
    val os = TextIO.openAppend "/tmp/isabelle_sh_results.txt"
    val _ = TextIO.output (os, line ^ "\n")
    val _ = TextIO.closeOut os
  in () end
  handle IO.Io _ => ()

local

fun run_sh_prover ctxt fact_override i th =
  let
    open Sledgehammer_Util Sledgehammer_Fact Sledgehammer_Prover
         Sledgehammer_Prover_Minimize Sledgehammer_MaSh Sledgehammer_Commands
    val thy = Proof_Context.theory_of ctxt
    val params as {provers, induction_rules, max_facts, ...} =
      default_params thy [("preplay_timeout", "0")]
    val name = hd provers
    val prover = get_prover ctxt Normal name
    val default_max_facts = #4 (fst (hd (get_slices ctxt name)))
    val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal th i ctxt
    val keywords = Thy_Header.get_keywords' ctxt
    val css_table = clasimpset_rule_table_of ctxt
    val inst_inducts = induction_rules = SOME Instantiate
    val facts =
      nearly_all_facts ctxt inst_inducts fact_override keywords css_table
        [] hyp_ts concl_t
      |> relevant_facts ctxt params name
           (the_default default_max_facts max_facts) fact_override hyp_ts concl_t
      |> hd |> snd
    val problem =
      {comment = "", state = Proof.init ctxt, goal = th,
       subgoal = i, subgoal_count = i,
       factss = [("", facts)],
       has_already_found_something = K false,
       found_something = K (),
       memoize_fun_call = fn f => f}
  in
    (case prover params problem (hd (get_slices ctxt name)) of
       {outcome = NONE, used_facts, ...} => used_facts |> map fst |> SOME
     | _ => NONE)
    handle ERROR msg => (warning ("sh prover: " ^ msg); NONE)
  end

(* Try tac; return SOME (label, first_result_state) if it succeeds. *)
fun try1 label tac =
  case Seq.pull tac of
    SOME (st, _) => SOME (label, st)
  | NONE => NONE

in

val _ = Theory.setup
  (Method.setup \<^binding>\<open>sh\<close>
    (Scan.succeed (fn ctxt =>
      Method.SIMPLE_METHOD' (fn i => fn th =>
        let
          (* Source location of this `by sh` invocation *)
          val pos  = Position.thread_data ()
          val file = the_default "?" (Position.file_of pos)
          val line = the_default 0   (Position.line_of pos)
          val loc  = file ^ ":" ^ Int.toString line

          val goal_str =
            Logic.get_goal (Thm.prop_of th) i
            |> Syntax.string_of_term ctxt
            |> YXML.parse_body |> XML.content_of
            |> (fn s => String.substring (s, 0, Int.min (80, String.size s)))

          (* Run ATP prover to get candidate facts *)
          val fact_names_opt =
            run_sh_prover ctxt Sledgehammer_Fact.no_fact_override i th

          (* Build tactic candidates: metis with ATP facts, then simp, then auto *)
          val fact_thms =
            case fact_names_opt of
              SOME ns => maps (Sledgehammer_Util.thms_of_name ctxt) ns
            | NONE => []

          val metis_label =
            "by (metis " ^
            String.concatWith " " (the_default [] fact_names_opt) ^ ")"

          val candidate =
            (case fact_names_opt of
               SOME _ =>
                 try1 metis_label
                   (Metis_Tactic.metis_tac []
                     ATP_Problem_Generate.combs_or_liftingN ctxt fact_thms i th)
             | NONE => NONE)
            |> (fn NONE =>
                  try1 "by (simp add: ...)"
                    (Simplifier.asm_full_simp_tac
                       (fold Simplifier.add_simp fact_thms ctxt) i th)
                | r => r)
            |> (fn NONE =>
                  try1 "by auto"
                    (auto_tac ctxt th)
                | r => r)
        in
          case candidate of
            SOME (label, st) =>
              (sh_record (loc ^ " | " ^ goal_str ^ " | " ^ label);
               Seq.single st)
          | NONE => Seq.empty
        end
        handle ERROR _ => Seq.empty)))
    "sh: ATP + metis/simp/auto; records result in /tmp/isabelle_sh_results.txt")

end

\<close>

end
