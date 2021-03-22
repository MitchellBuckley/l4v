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

(* Definitions should be written over 2 lines in the following two style.

   Note that indentation is 2 spaces and the definitions do not run past 100 character line
   limit. Note also that the \equiv symbol is used.
 *)

definition hd_opt :: "'a list \<Rightarrow> 'a option" where
  "hd_opt \<equiv> case_list None (\<lambda>h t. Some h)"

(* In the case that the type_signature causes an overflow of the 100 char line limit,
   use the following pattern.

   Note that the indentation of the type signature remains no less than the indentation level of
   the initial `"`.
 *)

type_synonym my_very_long_nat_type = nat
type_synonym 'a my_very_long_option_type = "'a option"
type_synonym 'a my_very_long_list_type = "'a list"
definition hd_opt2 :: "'a my_very_long_list_type \<Rightarrow> my_very_long_nat_type \<Rightarrow>
                       'a my_very_long_list_type \<Rightarrow> 'a my_very_long_option_type" where
  "hd_opt2 dummy_list dummy_nat \<equiv> case_list None (\<lambda>h t. Some h)"

(* In the case that the definition body causes an overflow of the 100 char line limit, use one
   of the following two patterns.

   Note that in each case, indentation of the right-hand expression remains no less than the
   indentation level of `case_list`.
 *)

definition hd_opt3 :: "'a list \<Rightarrow> 'a option" where
  "hd_opt3 \<equiv> case_list
             None
             (\<lambda>h t. Some h)"

definition hd_opt4 :: "'a list \<Rightarrow> 'a option" where
  "hd_opt4 \<equiv>
   case_list None (\<lambda>h t. Some h)"

section \<open>Lemma Statements\<close>


section \<open>Proofs\<close>


end
