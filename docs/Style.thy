(*
 * Copyright 2019, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

chapter \<open>An Isabelle Syntax Style Guide\<close>

theory Style
  imports Main
begin


section \<open>General Principles\<close>


section \<open>Definitions\<close>

(* Definitions should be written over 2 lines or 4 lines in one of the following two styles.

   Note that indentation is 2 spaces and the definitions do not run past 100 character line
   limit. Note also that the \equiv symbol is used.

   FIXME: Do others agree? Mitch.
 *)

definition
  hd_opt :: "'a list \<Rightarrow> 'a option"
where
  "hd_opt \<equiv> case_list None (\<lambda>h t. Some h)"

definition hd_opt2 :: "'a list \<Rightarrow> 'a option" where
  "hd_opt2 \<equiv> case_list None (\<lambda>h t. Some h)"

section \<open>Lemma Statements\<close>


section \<open>Proofs\<close>


end
