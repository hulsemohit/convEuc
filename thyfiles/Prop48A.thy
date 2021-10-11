theory Prop48A
	imports Euclid4 Geometry NCdistinct NCorder Prop04 Prop34 betweennotequal congruenceflip crossimpliesopposite equalanglesNC equalangleshelper equalanglesreflexive equalanglessymmetric equaltorightisright lessthancongruence lessthancongruence2 parallelNC ray4 squareparallelogram squarerectangle trichotomy1
begin

theorem(in euclidean_geometry) Prop48A:
	assumes 
		"square A B C D"
		"square a b c d"
		"qua_eq_area A B C D a b c d"
	shows "seg_eq A B a b"
proof -
	have "parallelogram A B C D" using squareparallelogram[OF `square A B C D`] .
	have "parallelogram a b c d" using squareparallelogram[OF `square a b c d`] .
	have "tri_cong B A D D C B" using Prop34[OF `parallelogram A B C D`] by blast
	have "tri_cong b a d d c b" using Prop34[OF `parallelogram a b c d`] by blast
	have "tri_eq_area B A D D C B" using congruentequalE[OF `tri_cong B A D D C B`] .
	have "tri_eq_area b a d d c b" using congruentequalE[OF `tri_cong b a d d c b`] .
	have "tri_eq_area B A D B D C" using ETpermutationE[OF `tri_eq_area B A D D C B`] by blast
	have "tri_eq_area B D C B A D" using ETsymmetricE[OF `tri_eq_area B A D B D C`] .
	have "tri_eq_area B D C A B D" using ETpermutationE[OF `tri_eq_area B D C B A D`] by blast
	have "tri_eq_area A B D B D C" using ETsymmetricE[OF `tri_eq_area B D C A B D`] .
	have "tri_eq_area b a d b d c" using ETpermutationE[OF `tri_eq_area b a d d c b`] by blast
	have "tri_eq_area b d c b a d" using ETsymmetricE[OF `tri_eq_area b a d b d c`] .
	have "tri_eq_area b d c a b d" using ETpermutationE[OF `tri_eq_area b d c b a d`] by blast
	have "tri_eq_area a b d b d c" using ETsymmetricE[OF `tri_eq_area b d c a b d`] .
	have "rectangle A B C D" using squarerectangle[OF `square A B C D`] .
	have "rectangle a b c d" using squarerectangle[OF `square a b c d`] .
	have "cross A C B D" using rectangle_f[OF `rectangle A B C D`] by blast
	have "cross a c b d" using rectangle_f[OF `rectangle a b c d`] by blast
	have "parallel A B C D" using parallelogram_f[OF `parallelogram A B C D`] by blast
	have "\<not> col A B D" using parallelNC[OF `parallel A B C D`] by blast
	have "parallel a b c d" using parallelogram_f[OF `parallelogram a b c d`] by blast
	have "\<not> col a b d" using parallelNC[OF `parallel a b c d`] by blast
	have "oppo_side A B D C" using crossimpliesopposite[OF `cross A C B D` `\<not> col A B D`] by blast
	have "oppo_side a b d c" using crossimpliesopposite[OF `cross a c b d` `\<not> col a b d`] by blast
	have "tri_eq_area A B D a b d" using halvesofequalsE[OF `tri_eq_area A B D B D C` `oppo_side A B D C` `tri_eq_area a b d b d c` `oppo_side a b d c` `qua_eq_area A B C D a b c d`] .
	have "seg_eq a b d a" using square_f[OF `square a b c d`] by blast
	have "seg_eq A B D A" using square_f[OF `square A B C D`] by blast
	have "seg_eq a b a d" using congruenceflip[OF `seg_eq a b d a`] by blast
	have "seg_eq A B A D" using congruenceflip[OF `seg_eq A B D A`] by blast
	have "\<not> (seg_lt a b A B)"
	proof (rule ccontr)
		assume "\<not> (\<not> (seg_lt a b A B))"
hence "seg_lt a b A B" by blast
		obtain E where "bet A E B \<and> seg_eq A E a b" using lessthan_f[OF `seg_lt a b A B`]  by  blast
		have "bet A E B" using `bet A E B \<and> seg_eq A E a b` by blast
		have "seg_eq A E a b" using `bet A E B \<and> seg_eq A E a b` by blast
		have "seg_lt a d A B" using lessthancongruence2[OF `seg_lt a b A B` `seg_eq a b a d`] .
		have "seg_lt a d A D" using lessthancongruence[OF `seg_lt a d A B` `seg_eq A B A D`] .
		obtain F where "bet A F D \<and> seg_eq A F a d" using lessthan_f[OF `seg_lt a d A D`]  by  blast
		have "bet A F D" using `bet A F D \<and> seg_eq A F a d` by blast
		have "seg_eq A F a d" using `bet A F D \<and> seg_eq A F a d` by blast
		have "ang_right D A B" using square_f[OF `square A B C D`] by blast
		have "ang_right d a b" using square_f[OF `square a b c d`] by blast
		have "A \<noteq> D" using betweennotequal[OF `bet A F D`] by blast
		have "A \<noteq> B" using betweennotequal[OF `bet A E B`] by blast
		have "ray_on A D F" using ray4 `bet A F D \<and> seg_eq A F a d` `A \<noteq> D` by blast
		have "ray_on A B E" using ray4 `bet A E B \<and> seg_eq A E a b` `A \<noteq> B` by blast
		have "\<not> col D A B" using NCorder[OF `\<not> col A B D`] by blast
		have "ang_eq D A B D A B" using equalanglesreflexive[OF `\<not> col D A B`] .
		have "ang_eq D A B F A E" using equalangleshelper[OF `ang_eq D A B D A B` `ray_on A D F` `ray_on A B E`] .
		have "ang_eq F A E D A B" using equalanglessymmetric[OF `ang_eq D A B F A E`] .
		have "ang_right F A E" using equaltorightisright[OF `ang_right D A B` `ang_eq F A E D A B`] .
		have "ang_eq F A E d a b" using Euclid4[OF `ang_right F A E` `ang_right d a b`] .
		have "seg_eq F E d b" using Prop04[OF `seg_eq A F a d` `seg_eq A E a b` `ang_eq F A E d a b`] by blast
		have "seg_eq F A d a" using congruenceflip[OF `seg_eq A F a d`] by blast
		have "seg_eq A E a b" using `seg_eq A E a b` .
		have "\<not> col F A E" using equalanglesNC[OF `ang_eq D A B F A E`] .
		have "triangle F A E" using triangle_b[OF `\<not> col F A E`] .
		have "tri_cong F A E d a b" using trianglecongruence_b[OF `seg_eq F A d a` `seg_eq A E a b` `seg_eq F E d b` `triangle F A E`] .
		have "tri_eq_area F A E d a b" using congruentequalE[OF `tri_cong F A E d a b`] .
		have "tri_eq_area F A E a b d" using ETpermutationE[OF `tri_eq_area F A E d a b`] by blast
		have "tri_eq_area a b d A B D" using ETsymmetricE[OF `tri_eq_area A B D a b d`] .
		have "tri_eq_area F A E A B D" using ETtransitiveE[OF `tri_eq_area F A E a b d` `tri_eq_area a b d A B D`] .
		have "tri_eq_area F A E D A B" using ETpermutationE[OF `tri_eq_area F A E A B D`] by blast
		have "tri_eq_area D A B F A E" using ETsymmetricE[OF `tri_eq_area F A E D A B`] .
		have "triangle D A B" using triangle_b[OF `\<not> col D A B`] .
		have "bet A F D" using `bet A F D` .
		have "bet A E B" using `bet A E B` .
		have "\<not> (tri_eq_area D A B F A E)" using deZolt2E[OF `triangle D A B` `bet A F D` `bet A E B`] .
		show "False" using `\<not> (tri_eq_area D A B F A E)` `tri_eq_area D A B F A E` by blast
	qed
	hence "\<not> (seg_lt a b A B)" by blast
	have "\<not> (seg_lt A B a b)"
	proof (rule ccontr)
		assume "\<not> (\<not> (seg_lt A B a b))"
hence "seg_lt A B a b" by blast
		obtain e where "bet a e b \<and> seg_eq a e A B" using lessthan_f[OF `seg_lt A B a b`]  by  blast
		have "bet a e b" using `bet a e b \<and> seg_eq a e A B` by blast
		have "seg_eq a e A B" using `bet a e b \<and> seg_eq a e A B` by blast
		have "seg_lt A D a b" using lessthancongruence2[OF `seg_lt A B a b` `seg_eq A B A D`] .
		have "seg_lt A D a d" using lessthancongruence[OF `seg_lt A D a b` `seg_eq a b a d`] .
		obtain f where "bet a f d \<and> seg_eq a f A D" using lessthan_f[OF `seg_lt A D a d`]  by  blast
		have "bet a f d" using `bet a f d \<and> seg_eq a f A D` by blast
		have "seg_eq a f A D" using `bet a f d \<and> seg_eq a f A D` by blast
		have "ang_right d a b" using square_f[OF `square a b c d`] by blast
		have "ang_right D A B" using square_f[OF `square A B C D`] by blast
		have "a \<noteq> d" using betweennotequal[OF `bet a f d`] by blast
		have "a \<noteq> b" using betweennotequal[OF `bet a e b`] by blast
		have "ray_on a d f" using ray4 `bet a f d \<and> seg_eq a f A D` `a \<noteq> d` by blast
		have "ray_on a b e" using ray4 `bet a e b \<and> seg_eq a e A B` `a \<noteq> b` by blast
		have "\<not> col d a b" using NCorder[OF `\<not> col a b d`] by blast
		have "ang_eq d a b d a b" using equalanglesreflexive[OF `\<not> col d a b`] .
		have "ang_eq d a b f a e" using equalangleshelper[OF `ang_eq d a b d a b` `ray_on a d f` `ray_on a b e`] .
		have "ang_eq f a e d a b" using equalanglessymmetric[OF `ang_eq d a b f a e`] .
		have "ang_right f a e" using equaltorightisright[OF `ang_right d a b` `ang_eq f a e d a b`] .
		have "ang_eq f a e D A B" using Euclid4[OF `ang_right f a e` `ang_right D A B`] .
		have "seg_eq f e D B" using Prop04[OF `seg_eq a f A D` `seg_eq a e A B` `ang_eq f a e D A B`] by blast
		have "seg_eq f a D A" using congruenceflip[OF `seg_eq a f A D`] by blast
		have "seg_eq a e A B" using `seg_eq a e A B` .
		have "\<not> col f a e" using equalanglesNC[OF `ang_eq d a b f a e`] .
		have "triangle f a e" using triangle_b[OF `\<not> col f a e`] .
		have "tri_cong f a e D A B" using trianglecongruence_b[OF `seg_eq f a D A` `seg_eq a e A B` `seg_eq f e D B` `triangle f a e`] .
		have "tri_eq_area f a e D A B" using congruentequalE[OF `tri_cong f a e D A B`] .
		have "tri_eq_area f a e A B D" using ETpermutationE[OF `tri_eq_area f a e D A B`] by blast
		have "tri_eq_area f a e a b d" using ETtransitiveE[OF `tri_eq_area f a e A B D` `tri_eq_area A B D a b d`] .
		have "tri_eq_area f a e d a b" using ETpermutationE[OF `tri_eq_area f a e a b d`] by blast
		have "tri_eq_area d a b f a e" using ETsymmetricE[OF `tri_eq_area f a e d a b`] .
		have "triangle d a b" using triangle_b[OF `\<not> col d a b`] .
		have "bet a f d" using `bet a f d` .
		have "bet a e b" using `bet a e b` .
		have "\<not> (tri_eq_area d a b f a e)" using deZolt2E[OF `triangle d a b` `bet a f d` `bet a e b`] .
		show "False" using `\<not> (tri_eq_area d a b f a e)` `tri_eq_area d a b f a e` by blast
	qed
	hence "\<not> (seg_lt A B a b)" by blast
	have "A \<noteq> B" using NCdistinct[OF `\<not> col A B D`] by blast
	have "a \<noteq> b" using NCdistinct[OF `\<not> col a b d`] by blast
	have "seg_eq A B a b" using trichotomy1[OF `\<not> (seg_lt A B a b)` `\<not> (seg_lt a b A B)` `A \<noteq> B` `a \<noteq> b`] .
	thus ?thesis by blast
qed

end