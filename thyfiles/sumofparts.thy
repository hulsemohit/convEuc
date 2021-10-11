theory sumofparts
	imports Geometry congruencetransitive
begin

theorem(in euclidean_geometry) sumofparts:
	assumes 
		"seg_eq A B a b"
		"seg_eq B C b c"
		"bet A B C"
		"bet a b c"
	shows "seg_eq A C a c"
proof -
	have "seg_eq A A a a" using nullsegment2E.
	have "seg_eq B A A B" using equalityreverseE.
	have "seg_eq a b b a" using equalityreverseE.
	have "seg_eq B A a b" using congruencetransitive[OF `seg_eq B A A B` `seg_eq A B a b`] .
	have "seg_eq B A b a" using congruencetransitive[OF `seg_eq B A a b` `seg_eq a b b a`] .
	have "seg_eq A C a c" using n5_lineE[OF `seg_eq B C b c` `seg_eq A A a a` `seg_eq B A b a` `bet A B C` `bet a b c` `seg_eq A B a b`] .
	thus ?thesis by blast
qed

end