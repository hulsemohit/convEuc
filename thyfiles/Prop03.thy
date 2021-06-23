theory Prop03
	imports Geometry congruencesymmetric lessthancongruence
begin

theorem Prop03:
	assumes "axioms"
		"seg_lt C D A B"
		"seg_eq E F A B"
	shows "\<exists> G. bet E G F \<and> seg_eq E G C D"
proof -
	have "seg_eq A B E F" using congruencesymmetric[OF `axioms` `seg_eq E F A B`] .
	have "seg_lt C D E F" using lessthancongruence[OF `axioms` `seg_lt C D A B` `seg_eq A B E F`] .
	obtain G where "bet E G F \<and> seg_eq E G C D" using lessthan_f[OF `axioms` `seg_lt C D E F`]  by  blast
	thus ?thesis by blast
qed

end