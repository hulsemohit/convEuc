theory EFreflexive
	imports Geometry NCorder TCreflexive betweennotequal collinear4 collinearorder inequalitysymmetric
begin

theorem(in euclidean_geometry) EFreflexive:
	assumes 
		"bet a p c"
		"bet b p d"
		"\<not> col a b c"
	shows "qua_eq_area a b c d a b c d"
proof -
	have "\<not> col a c b" using NCorder[OF `\<not> col a b c`] by blast
	have "\<not> (col a c d)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col a c d))"
hence "col a c d" by blast
		have "col b p d" using collinear_b `bet b p d` by blast
		have "col a p c" using collinear_b `bet a p c` by blast
		have "col a c p" using collinearorder[OF `col a p c`] by blast
		have "a \<noteq> c" using betweennotequal[OF `bet a p c`] by blast
		have "col c d p" using collinear4[OF `col a c d` `col a c p` `a \<noteq> c`] .
		have "col d p c" using collinearorder[OF `col c d p`] by blast
		have "col d p b" using collinearorder[OF `col b p d`] by blast
		have "p \<noteq> d" using betweennotequal[OF `bet b p d`] by blast
		have "d \<noteq> p" using inequalitysymmetric[OF `p \<noteq> d`] .
		have "col p c b" using collinear4[OF `col d p c` `col d p b` `d \<noteq> p`] .
		have "col a p c" using collinear_b `bet a p c` by blast
		have "col p c a" using collinearorder[OF `col a c p`] by blast
		have "p \<noteq> c" using betweennotequal[OF `bet a p c`] by blast
		have "col c b a" using collinear4[OF `col p c b` `col p c a` `p \<noteq> c`] .
		have "col a b c" using collinearorder[OF `col c b a`] by blast
		show "False" using `col a b c` `\<not> col a b c` by blast
	qed
	hence "\<not> col a c d" by blast
	have "triangle a c d" using triangle_b[OF `\<not> col a c d`] .
	have "triangle a c b" using triangle_b[OF `\<not> col a c b`] .
	have "tri_cong a c d a c d" using TCreflexive[OF `triangle a c d`] .
	have "tri_cong a c b a c b" using TCreflexive[OF `triangle a c b`] .
	have "tri_eq_area a c d a c d" using congruentequalE[OF `tri_cong a c d a c d`] .
	have "tri_eq_area a c b a c b" using congruentequalE[OF `tri_cong a c b a c b`] .
	have "col a c p" using collinear_b `bet a p c` by blast
	have "\<not> col a c b" using NCorder[OF `\<not> col a b c`] by blast
	have "oppo_side b a c d" using oppositeside_b[OF `bet b p d` `col a c p` `\<not> col a c b`] .
	have "qua_eq_area a b c d a b c d" using paste3E `tri_eq_area a c b a c b` `tri_eq_area a c d a c d` `bet b p d` `bet a p c` `bet b p d` `bet a p c` by blast
	thus ?thesis by blast
qed

end