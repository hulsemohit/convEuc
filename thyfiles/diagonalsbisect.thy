theory diagonalsbisect
	imports ABCequalsCBA Geometry NCdistinct NChelper NCorder Prop26A Prop29B Prop34 betweennotequal collinear4 collinearorder congruenceflip crossimpliesopposite diagonalsmeet equalanglesflip equalangleshelper equalanglesreflexive equalanglessymmetric equalanglestransitive inequalitysymmetric parallelNC parallelflip ray4
begin

theorem(in euclidean_geometry) diagonalsbisect:
	assumes 
		"parallelogram A B C D"
	shows "\<exists> M. midpoint A M C \<and> midpoint B M D"
proof -
	obtain M where "bet A M C \<and> bet B M D" using diagonalsmeet[OF `parallelogram A B C D`]  by  blast
	have "bet A M C" using `bet A M C \<and> bet B M D` by blast
	have "bet B M D" using `bet A M C \<and> bet B M D` by blast
	have "parallel A B C D \<and> parallel A D B C" using parallelogram_f[OF `parallelogram A B C D`] .
	have "A \<noteq> C" using betweennotequal[OF `bet A M C`] by blast
	have "B \<noteq> D" using betweennotequal[OF `bet B M D`] by blast
	have "cross A C B D" using cross_b[OF `bet A M C` `bet B M D`] .
	have "parallel A B C D" using parallelogram_f[OF `parallelogram A B C D`] by blast
	have "parallel A B D C" using parallelflip[OF `parallel A B C D`] by blast
	have "\<not> col A B D" using parallelNC[OF `parallel A B C D`] by blast
	have "oppo_side A B D C" using crossimpliesopposite[OF `cross A C B D` `\<not> col A B D`] by blast
	have "parallel B A D C" using parallelflip[OF `parallel A B C D`] by blast
	have "bet C M A" using betweennesssymmetryE[OF `bet A M C`] .
	have "bet D M B" using betweennesssymmetryE[OF `bet B M D`] .
	have "cross B D A C" using cross_b[OF `bet B M D` `bet A M C`] .
	have "\<not> col A B C" using parallelNC[OF `parallel A B C D`] by blast
	have "\<not> col B A C" using NCorder[OF `\<not> col A B C`] by blast
	have "oppo_side B A C D" using crossimpliesopposite[OF `cross B D A C` `\<not> col B A C`] by blast
	have "seg_eq A B D C" using Prop34[OF `parallelogram A B C D`] by blast
	have "seg_eq A B C D" using congruenceflip[OF `seg_eq A B D C`] by blast
	have "\<not> (col M A B)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col M A B))"
hence "col M A B" by blast
		have "col A M C" using collinear_b `bet A M C \<and> bet B M D` by blast
		have "col M A C" using collinearorder[OF `col A M C`] by blast
		have "A \<noteq> M" using betweennotequal[OF `bet A M C`] by blast
		have "M \<noteq> A" using inequalitysymmetric[OF `A \<noteq> M`] .
		have "col A B C" using collinear4[OF `col M A B` `col M A C` `M \<noteq> A`] .
		have "\<not> col A B C" using parallelNC[OF `parallel A B C D`] by blast
		show "False" using `\<not> col A B C` `col A B C` by blast
	qed
	hence "\<not> col M A B" by blast
	have "triangle M A B" using triangle_b[OF `\<not> col M A B`] .
	have "\<not> (col M C D)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col M C D))"
hence "col M C D" by blast
		have "col A M C" using collinear_b `bet A M C \<and> bet B M D` by blast
		have "col M C A" using collinearorder[OF `col A M C`] by blast
		have "M \<noteq> C" using betweennotequal[OF `bet A M C`] by blast
		have "col C D A" using collinear4[OF `col M C D` `col M C A` `M \<noteq> C`] .
		have "col A C D" using collinearorder[OF `col C D A`] by blast
		have "\<not> col A C D" using parallelNC[OF `parallel A B C D`] by blast
		show "False" using `\<not> col A C D` `col A C D` by blast
	qed
	hence "\<not> col M C D" by blast
	have "triangle M C D" using triangle_b[OF `\<not> col M C D`] .
	have "seg_eq A B C D" using `seg_eq A B C D` .
	have "parallel A B C D" using `parallel A B C D` .
	have "parallel B A C D" using parallelflip[OF `parallel A B C D`] by blast
	have "oppo_side B A C D" using `oppo_side B A C D` .
	have "ang_eq B A C A C D" using Prop29B[OF `parallel B A C D` `oppo_side B A C D`] .
	have "ang_eq B A C B A C" using equalanglesreflexive[OF `\<not> col B A C`] .
	have "ray_on A C M" using ray4 `bet A M C \<and> bet B M D` `A \<noteq> C` by blast
	have "B = B" using equalityreflexiveE.
	have "\<not> col A B C" using parallelNC[OF `parallel A B C D`] by blast
	have "A \<noteq> B" using NCdistinct[OF `\<not> col A B C`] by blast
	have "ray_on A B B" using ray4 `B = B` `A \<noteq> B` by blast
	have "ang_eq B A C B A M" using equalangleshelper[OF `ang_eq B A C B A C` `ray_on A B B` `ray_on A C M`] .
	have "ang_eq B A M B A C" using equalanglessymmetric[OF `ang_eq B A C B A M`] .
	have "ang_eq B A M A C D" using equalanglestransitive[OF `ang_eq B A M B A C` `ang_eq B A C A C D`] .
	have "D = D" using equalityreflexiveE.
	have "\<not> col A C D" using parallelNC[OF `parallel A B C D`] by blast
	have "C \<noteq> D" using NCdistinct[OF `\<not> col A C D`] by blast
	have "C \<noteq> A" using NCdistinct[OF `\<not> col A B C`] by blast
	have "ray_on C D D" using ray4 `D = D` `C \<noteq> D` by blast
	have "ray_on C A M" using ray4 `bet C M A` `C \<noteq> A` by blast
	have "ang_eq A C D A C D" using equalanglesreflexive[OF `\<not> col A C D`] .
	have "ang_eq A C D M C D" using equalangleshelper[OF `ang_eq A C D A C D` `ray_on C A M` `ray_on C D D`] .
	have "ang_eq B A M M C D" using equalanglestransitive[OF `ang_eq B A M A C D` `ang_eq A C D M C D`] .
	have "\<not> col A C D" using parallelNC[OF `parallel A B C D`] by blast
	have "col A M C" using collinear_b `bet A M C \<and> bet B M D` by blast
	have "col A C M" using collinearorder[OF `col A M C`] by blast
	have "C = C" using equalityreflexiveE.
	have "col A C C" using collinear_b `C = C` by blast
	have "M \<noteq> C" using betweennotequal[OF `bet A M C`] by blast
	have "\<not> col M C D" using NChelper[OF `\<not> col A C D` `col A C M` `col A C C` `M \<noteq> C`] .
	have "ang_eq M C D D C M" using ABCequalsCBA[OF `\<not> col M C D`] .
	have "ang_eq B A M D C M" using equalanglestransitive[OF `ang_eq B A M M C D` `ang_eq M C D D C M`] .
	have "parallel A B D C" using parallelflip[OF `parallel A B C D`] by blast
	have "oppo_side A B D C" using `oppo_side A B D C` .
	have "ang_eq A B D B D C" using Prop29B[OF `parallel A B D C` `oppo_side A B D C`] .
	have "ang_eq A B D A B D" using equalanglesreflexive[OF `\<not> col A B D`] .
	have "ray_on B D M" using ray4 `bet A M C \<and> bet B M D` `B \<noteq> D` by blast
	have "A = A" using equalityreflexiveE.
	have "\<not> col B A D" using parallelNC[OF `parallel B A C D`] by blast
	have "B \<noteq> A" using NCdistinct[OF `\<not> col A B C`] by blast
	have "ray_on B A A" using ray4 `A = A` `B \<noteq> A` by blast
	have "ang_eq A B D A B M" using equalangleshelper[OF `ang_eq A B D A B D` `ray_on B A A` `ray_on B D M`] .
	have "ang_eq A B M A B D" using equalanglessymmetric[OF `ang_eq A B D A B M`] .
	have "ang_eq A B M B D C" using equalanglestransitive[OF `ang_eq A B M A B D` `ang_eq A B D B D C`] .
	have "C = C" using equalityreflexiveE.
	have "\<not> col B D C" using parallelNC[OF `parallel A B D C`] by blast
	have "D \<noteq> C" using NCdistinct[OF `\<not> col A C D`] by blast
	have "D \<noteq> B" using NCdistinct[OF `\<not> col A B D`] by blast
	have "ray_on D C C" using ray4 `C = C` `D \<noteq> C` by blast
	have "ray_on D B M" using ray4 `bet D M B` `D \<noteq> B` by blast
	have "ang_eq B D C B D C" using equalanglesreflexive[OF `\<not> col B D C`] .
	have "ang_eq B D C M D C" using equalangleshelper[OF `ang_eq B D C B D C` `ray_on D B M` `ray_on D C C`] .
	have "ang_eq A B M M D C" using equalanglestransitive[OF `ang_eq A B M B D C` `ang_eq B D C M D C`] .
	have "\<not> col B D C" using parallelNC[OF `parallel A B D C`] by blast
	have "col B M D" using collinear_b `bet A M C \<and> bet B M D` by blast
	have "col B D M" using collinearorder[OF `col B M D`] by blast
	have "D = D" using equalityreflexiveE.
	have "col B D D" using collinear_b `D = D` by blast
	have "M \<noteq> D" using betweennotequal[OF `bet B M D`] by blast
	have "\<not> col M D C" using NChelper[OF `\<not> col B D C` `col B D M` `col B D D` `M \<noteq> D`] .
	have "ang_eq M D C C D M" using ABCequalsCBA[OF `\<not> col M D C`] .
	have "ang_eq A B M C D M" using equalanglestransitive[OF `ang_eq A B M M D C` `ang_eq M D C C D M`] .
	have "ang_eq M A B M C D" using equalanglesflip[OF `ang_eq B A M D C M`] .
	have "seg_eq M A M C \<and> seg_eq M B M D \<and> ang_eq A M B C M D" using Prop26A[OF `triangle M A B` `triangle M C D` `ang_eq M A B M C D` `ang_eq A B M C D M` `seg_eq A B C D`] .
	have "seg_eq M A M C" using `seg_eq M A M C \<and> seg_eq M B M D \<and> ang_eq A M B C M D` by blast
	have "seg_eq M B M D" using `seg_eq M A M C \<and> seg_eq M B M D \<and> ang_eq A M B C M D` by blast
	have "seg_eq A M M C" using congruenceflip[OF `seg_eq M A M C`] by blast
	have "seg_eq B M M D" using congruenceflip[OF `seg_eq M B M D`] by blast
	have "midpoint A M C" using midpoint_b[OF `bet A M C` `seg_eq A M M C`] .
	have "midpoint B M D" using midpoint_b[OF `bet B M D` `seg_eq B M M D`] .
	have "midpoint A M C \<and> midpoint B M D" using `midpoint A M C` `midpoint B M D` by blast
	thus ?thesis by blast
qed

end