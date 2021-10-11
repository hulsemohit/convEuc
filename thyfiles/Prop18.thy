theory Prop18
	imports ABCequalsCBA Geometry Prop03 Prop05 Prop16 angleorderrespectscongruence angleorderrespectscongruence2 angleordertransitive betweennotequal collinear4 collinearorder equalangleshelper equalanglesreflexive equalanglessymmetric inequalitysymmetric ray4
begin

theorem(in euclidean_geometry) Prop18:
	assumes 
		"triangle A B C"
		"seg_lt A B A C"
	shows "ang_lt B C A A B C"
proof -
	have "\<not> col A B C" using triangle_f[OF `triangle A B C`] .
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> B)"
		hence "A = B" by blast
		have "col A B C" using collinear_b `A = B` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> B" by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
	have "\<not> (A = C)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> C)"
		hence "A = C" by blast
		have "col A B C" using collinear_b `A = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> C" by blast
	have "C \<noteq> A" using inequalitysymmetric[OF `A \<noteq> C`] .
	have "seg_eq A C A C" using congruencereflexiveE.
	obtain D where "bet A D C \<and> seg_eq A D A B" using Prop03[OF `seg_lt A B A C` `seg_eq A C A C`]  by  blast
	have "bet A D C" using `bet A D C \<and> seg_eq A D A B` by blast
	have "\<not> (col B C D)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col B C D))"
hence "col B C D" by blast
		have "col D C B" using collinearorder[OF `col B C D`] by blast
		have "col A D C" using collinear_b `bet A D C \<and> seg_eq A D A B` by blast
		have "col D C A" using collinearorder[OF `col A D C`] by blast
		have "D \<noteq> C" using betweennotequal[OF `bet A D C`] by blast
		have "col C B A" using collinear4[OF `col D C B` `col D C A` `D \<noteq> C`] .
		have "col A B C" using collinearorder[OF `col C B A`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col B C D" by blast
	have "triangle B C D" using triangle_b[OF `\<not> col B C D`] .
	have "bet C D A" using betweennesssymmetryE[OF `bet A D C`] .
	have "ang_lt D C B B D A" using Prop16[OF `triangle B C D` `bet C D A`] by blast
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> C)"
		hence "B = C" by blast
		have "col B C D" using collinear_b `B = C` by blast
		show "False" using `col B C D` `\<not> col B C D` by blast
	qed
	hence "B \<noteq> C" by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `B \<noteq> C`] .
	have "\<not> (col A D B)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col A D B))"
hence "col A D B" by blast
		have "col A D C" using collinear_b `bet A D C \<and> seg_eq A D A B` by blast
		have "col D A C" using collinearorder[OF `col A D C`] by blast
		have "col D A B" using collinearorder[OF `col A D B`] by blast
		have "A \<noteq> D" using betweennotequal[OF `bet A D C`] by blast
		have "D \<noteq> A" using inequalitysymmetric[OF `A \<noteq> D`] .
		have "col A C B" using collinear4[OF `col D A C` `col D A B` `D \<noteq> A`] .
		have "col A B C" using collinearorder[OF `col A C B`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col A D B" by blast
	have "triangle A D B" using triangle_b[OF `\<not> col A D B`] .
	have "seg_eq A D A B" using `bet A D C \<and> seg_eq A D A B` by blast
	have "tri_isos A D B" using isosceles_b[OF `triangle A D B` `seg_eq A D A B`] .
	have "ang_eq A D B A B D" using Prop05[OF `tri_isos A D B`] .
	have "ray_on C A D" using ray4 `bet C D A` `C \<noteq> A` by blast
	have "B = B" using equalityreflexiveE.
	have "ray_on C B B" using ray4 `B = B` `C \<noteq> B` by blast
	have "\<not> (col A C B)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col A C B))"
hence "col A C B" by blast
		have "col A B C" using collinearorder[OF `col A C B`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col A C B" by blast
	have "ang_eq A C B A C B" using equalanglesreflexive[OF `\<not> col A C B`] .
	have "ang_eq A C B D C B" using equalangleshelper[OF `ang_eq A C B A C B` `ray_on C A D` `ray_on C B B`] .
	have "ang_lt A C B B D A" using angleorderrespectscongruence2[OF `ang_lt D C B B D A` `ang_eq A C B D C B`] .
	have "ang_eq A D B B D A" using ABCequalsCBA[OF `\<not> col A D B`] .
	have "ang_lt A C B A D B" using angleorderrespectscongruence[OF `ang_lt A C B B D A` `ang_eq A D B B D A`] .
	have "ang_eq A D B A B D" using `ang_eq A D B A B D` .
	have "ang_eq A B D A D B" using equalanglessymmetric[OF `ang_eq A D B A B D`] .
	have "ang_lt A C B A B D" using angleorderrespectscongruence[OF `ang_lt A C B A D B` `ang_eq A B D A D B`] .
	have "\<not> (col B C A)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col B C A))"
hence "col B C A" by blast
		have "col A B C" using collinearorder[OF `col B C A`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col B C A" by blast
	have "ang_eq B C A A C B" using ABCequalsCBA[OF `\<not> col B C A`] .
	have "ang_lt B C A A B D" using angleorderrespectscongruence2[OF `ang_lt A C B A B D` `ang_eq B C A A C B`] .
	have "C = C" using equalityreflexiveE.
	have "A = A" using equalityreflexiveE.
	have "ray_on B C C" using ray4 `C = C` `B \<noteq> C` by blast
	have "ray_on B A A" using ray4 `A = A` `B \<noteq> A` by blast
	have "bet A D C" using `bet A D C` .
	have "\<not> (col A B D)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col A B D))"
hence "col A B D" by blast
		have "col A D B" using collinearorder[OF `col A B D`] by blast
		show "False" using `col A D B` `\<not> col A D B` by blast
	qed
	hence "\<not> col A B D" by blast
	have "ang_eq A B D A B D" using equalanglesreflexive[OF `\<not> col A B D`] .
	have "ang_lt A B D A B C" using anglelessthan_b[OF `bet A D C` `ray_on B A A` `ray_on B C C` `ang_eq A B D A B D`] .
	have "ang_lt B C A A B C" using angleordertransitive[OF `ang_lt B C A A B D` `ang_lt A B D A B C`] .
	thus ?thesis by blast
qed

end