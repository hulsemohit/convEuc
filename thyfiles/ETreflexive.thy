theory ETreflexive
	imports Geometry TCreflexive
begin

theorem ETreflexive:
	assumes "axioms"
		"triangle A B C"
	shows "tri_eq_area A B C A B C"
proof -
	have "tri_cong A B C A B C" using TCreflexive[OF `axioms` `triangle A B C`] .
	have "tri_eq_area A B C A B C" using congruentequalE[OF `axioms` `tri_cong A B C A B C`] .
	thus ?thesis by blast
qed

end