(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory parse_enum
imports "CParser.CTranslation"
begin

external_file "parse_enum.c"
install_C_file "parse_enum.c"

print_locale parse_enum_global_addresses


context parse_enum_global_addresses
begin
thm f_body_def
thm g_body_def
thm h_body_def
end

term winedark

thm winedark_def
thm claret_def
thm chartreuse_def
thm hue_defs
thm foo_defs

thm ts20091113_defs

lemma "bar2 = -9 & baz2 = -60 & quux = 2"
by (simp add: ts20091113_defs)

end
