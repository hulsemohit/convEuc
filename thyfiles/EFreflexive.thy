theory EFreflexive
	imports Axioms Definitions Theorems
begin

theorem EFreflexive:
	assumes: `axioms`
		"bet a p c"
		"bet b p d"
		"\<not> col a b c"
	shows: "qua_eq_area a b c d a b c d"
proof -
	have "\<not> col a c b" using NCorder[OF `axioms` `\<not> col a b c`] by blast
	have "\<not> (col a c d)"
	proof (rule ccontr)
		assume "col a c d"
		have "col b p d" using col_b `axioms` `bet b p d` by blast
		have "col a p c" using col_b `axioms` `bet a p c` by blast
		have "col a c p" using collinearorder[OF `axioms` `col a p c`] by blast
		have "a \<noteq> c" using betweennotequal[OF `axioms` `bet a p c`] by blast
		have "col c d p" using collinear4[OF `axioms` `col a c d` `col a c p` `a \<noteq> c`] .
		have "col d p c" using collinearorder[OF `axioms` `col c d p`] by blast
		have "col d p b" using collinearorder[OF `axioms` `col b p d`] by blast
		have "p \<noteq> d" using betweennotequal[OF `axioms` `bet b p d`] by blast
		have "d \<noteq> p" using inequalitysymmetric[OF `axioms` `p \<noteq> d`] .
		have "col p c b" using collinear4[OF `axioms` `col d p c` `col d p b` `d \<noteq> p`] .
		have "col a p c" using col_b `axioms` `bet a p c` by blast
		have "col p c a" using collinearorder[OF `axioms` `col a c p`] by blast
		have "p \<noteq> c" using betweennotequal[OF `axioms` `bet a p c`] by blast
		have "col c b a" using collinear4[OF `axioms` `col p c b` `col p c a` `p \<noteq> c`] .
		have "col a b c" using collinearorder[OF `axioms` `col c b a`] by blast
		show "False" using `col a b c` `\<not> col a b c` by blast
	qed
	hence "\<not> col a c d" by blast
	have "triangle a c d" sorry
	have "triangle a c b" sorry
	have "tri_cong a c d a c d" using TCreflexive[OF `axioms` `triangle a c d`] .
	have "tri_cong a c b a c b" using TCreflexive[OF `axioms` `triangle a c b`] .
	have "tri_eq_area a c d a c d" using congruentequalE[OF `axioms` `tri_cong a c d a c d`] .
	have "tri_eq_area a c b a c b" using congruentequalE[OF `axioms` `tri_cong a c b a c b`] .
	have "col a c p" using col_b `axioms` `bet a p c` by blast
	have "\<not> col a c b" using NCorder[OF `axioms` `\<not> col a b c`] by blast
	have "oppo_side b a c d" sorry
	have "qua_eq_area a b c d a b c d" sorry
	thus ?thesis by blast
qed

end