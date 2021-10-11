theory Prop47B
	imports n3_6b n8_2 n8_7 ABCequalsCBA Euclid4 Geometry NCdistinct NCorder PGflip Prop04 Prop34 Prop41 Prop47A angleaddition betweennotequal collinear4 collinearbetween collinearorder collinearparallel collinearright congruenceflip congruencesymmetric diagonalsbisect equalanglesNC equalangleshelper equalanglesreflexive equalanglessymmetric equalanglestransitive inequalitysymmetric oppositesideflip parallelNC paralleldef2B parallelflip parallelsymmetric planeseparation ray4 ray5 righttogether samesidesymmetric squareparallelogram
begin

theorem(in euclidean_geometry) Prop47B:
	assumes 
		"triangle A B C"
		"ang_right B A C"
		"square A B F G"
		"oppo_side G B A C"
		"square B C E D"
		"oppo_side D C B A"
	shows "\<exists> L M. parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A \<and> qua_eq_area A B F G B M L D"
proof -
	obtain L M where "parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A" using Prop47A[OF `triangle A B C` `ang_right B A C` `square B C E D` `oppo_side D C B A`]  by  blast
	have "parallelogram B M L D" using `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A` by blast
	have "bet B M C" using `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A` by blast
	have "parallelogram M C E L" using `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A` by blast
	have "bet D L E" using `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A` by blast
	have "bet L M A" using `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A` by blast
	have "ang_right D L A" using `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A` by blast
	obtain N where "bet D N A \<and> col C B N \<and> \<not> col C B D" using oppositeside_f[OF `oppo_side D C B A`]  by  blast
	have "ang_right G A B" using square_f[OF `square A B F G`] by blast
	have "bet G A C" using righttogether[OF `ang_right G A B` `ang_right B A C` `oppo_side G B A C`] by blast
	have "ang_right A B F" using square_f[OF `square A B F G`] by blast
	have "ang_right F B A" using n8_2[OF `ang_right A B F`] .
	have "ang_right D B C" using square_f[OF `square B C E D`] by blast
	have "\<not> col A B C" using triangle_f[OF `triangle A B C`] .
	have "parallelogram A B F G" using squareparallelogram[OF `square A B F G`] .
	have "parallel A B F G" using parallelogram_f[OF `parallelogram A B F G`] by blast
	have "parallel A B G F" using parallelflip[OF `parallel A B F G`] by blast
	have "tarski_parallel A B G F" using paralleldef2B[OF `parallel A B G F`] .
	have "same_side G F A B" using tarski_parallel_f[OF `tarski_parallel A B G F`] by blast
	have "same_side F G A B" using samesidesymmetric[OF `same_side G F A B`] by blast
	have "oppo_side G A B C" using oppositesideflip[OF `oppo_side G B A C`] .
	have "oppo_side F A B C" using planeseparation[OF `same_side F G A B` `oppo_side G A B C`] .
	obtain a where "bet F a C \<and> col A B a \<and> \<not> col A B F" using oppositeside_f[OF `oppo_side F A B C`]  by  blast
	have "bet F a C" using `bet F a C \<and> col A B a \<and> \<not> col A B F` by blast
	have "col A B a" using `bet F a C \<and> col A B a \<and> \<not> col A B F` by blast
	have "col B A a" using collinearorder[OF `col A B a`] by blast
	have "parallel A G B F" using parallelogram_f[OF `parallelogram A B F G`] by blast
	have "parallel A G F B" using parallelflip[OF `parallel A G B F`] by blast
	have "col G A C" using collinear_b `bet G A C` by blast
	have "col A G C" using collinearorder[OF `col G A C`] by blast
	have "G \<noteq> C" using betweennotequal[OF `bet G A C`] by blast
	have "C \<noteq> G" using inequalitysymmetric[OF `G \<noteq> C`] .
	have "parallel F B A G" using parallelsymmetric[OF `parallel A G F B`] .
	have "parallel F B C G" using collinearparallel[OF `parallel F B A G` `col A G C` `C \<noteq> G`] .
	have "parallel F B G C" using parallelflip[OF `parallel F B C G`] by blast
	have "\<not> (meets F B G C)" using parallel_f[OF `parallel F B G C`] by fastforce
	have "A \<noteq> C" using NCdistinct[OF `\<not> col A B C`] by blast
	have "\<not> col A B F" using parallelNC[OF `parallel A B F G`] by blast
	have "F \<noteq> A" using NCdistinct[OF `\<not> col A B F`] by blast
	have "F \<noteq> B" using NCdistinct[OF `\<not> col A B F`] by blast
	have "B = B" using equalityreflexiveE.
	have "col F B B" using collinear_b `B = B` by blast
	have "col F B B \<and> col G A C \<and> F \<noteq> B \<and> G \<noteq> C \<and> F \<noteq> A \<and> A \<noteq> C \<and> \<not> (meets F B G C) \<and> bet F a C \<and> col B A a" using `col F B B` `col G A C` `F \<noteq> B` `G \<noteq> C` `F \<noteq> A` `A \<noteq> C` `\<not> (meets F B G C)` `bet F a C \<and> col A B a \<and> \<not> col A B F` `col B A a` by blast
	have "bet B a A" using collinearbetween[OF `col F B B` `col G A C` `F \<noteq> B` `G \<noteq> C` `F \<noteq> B` `A \<noteq> C` `\<not> (meets F B G C)` `bet F a C` `col B A a`] .
	have "B \<noteq> a" using betweennotequal[OF `bet B a A`] by blast
	have "ray_on B a A" using ray4 `bet B a A` `B \<noteq> a` by blast
	have "B \<noteq> F" using inequalitysymmetric[OF `F \<noteq> B`] .
	have "F = F" using equalityreflexiveE.
	have "ray_on B F F" using ray4 `F = F` `B \<noteq> F` by blast
	have "\<not> col A B F" using parallelNC[OF `parallel A B F G`] by blast
	have "\<not> col F B A" using NCorder[OF `\<not> col A B F`] by blast
	have "ang_eq F B A F B A" using equalanglesreflexive[OF `\<not> col F B A`] .
	have "ray_on B A a" using ray5[OF `ray_on B a A`] .
	have "ang_eq F B A F B a" using equalangleshelper[OF `ang_eq F B A F B A` `ray_on B F F` `ray_on B A a`] .
	have "B \<noteq> C" using NCdistinct[OF `\<not> col A B C`] by blast
	have "C = C" using equalityreflexiveE.
	have "ray_on B C C" using ray4 `C = C` `B \<noteq> C` by blast
	have "ang_eq A B C A B C" using equalanglesreflexive[OF `\<not> col A B C`] .
	have "ang_eq A B C a B C" using equalangleshelper[OF `ang_eq A B C A B C` `ray_on B A a` `ray_on B C C`] .
	have "area_sum_eq F B A A B C F B C" using anglesum_b[OF `ang_eq F B A F B a` `ang_eq A B C a B C` `bet F a C`] .
	have "oppo_side D C B A" using `oppo_side D C B A` .
	obtain c where "bet D c A \<and> col C B c \<and> \<not> col C B D" using oppositeside_f[OF `oppo_side D C B A`]  by  blast
	have "bet D c A" using `bet D c A \<and> col C B c \<and> \<not> col C B D` by blast
	have "col C B c" using `bet D c A \<and> col C B c \<and> \<not> col C B D` by blast
	have "\<not> col C B D" using `bet D N A \<and> col C B N \<and> \<not> col C B D` by blast
	have "square B C E D" using `square B C E D` .
	have "parallelogram B C E D" using squareparallelogram[OF `square B C E D`] .
	have "parallel B D C E" using parallelogram_f[OF `parallelogram B C E D`] by blast
	have "parallel C E B D" using parallelsymmetric[OF `parallel B D C E`] .
	have "parallel C E D B" using parallelflip[OF `parallel C E B D`] by blast
	have "col B C c" using collinearorder[OF `col C B c`] by blast
	have "col B M C" using collinear_b `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A` by blast
	have "col C B M" using collinearorder[OF `col B M C`] by blast
	have "col C B c" using collinearorder[OF `col B C c`] by blast
	have "C \<noteq> B" using NCdistinct[OF `\<not> col A B C`] by blast
	have "col B M c" using collinear4[OF `col C B M` `col C B c` `C \<noteq> B`] .
	have "parallelogram B M L D" using `parallelogram B M L D` .
	have "parallel B D M L" using parallelogram_f[OF `parallelogram B M L D`] by blast
	have "col L M A" using collinear_b `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A` by blast
	have "col M L A" using collinearorder[OF `col L M A`] by blast
	have "L \<noteq> A" using betweennotequal[OF `bet L M A`] by blast
	have "A \<noteq> L" using inequalitysymmetric[OF `L \<noteq> A`] .
	have "parallel B D A L" using collinearparallel[OF `parallel B D M L` `col M L A` `A \<noteq> L`] .
	have "B = B" using equalityreflexiveE.
	have "parallel D B L A" using parallelflip[OF `parallel B D A L`] by blast
	have "\<not> (meets D B L A)" using parallel_f[OF `parallel D B L A`] by fastforce
	have "\<not> col B D L" using parallelNC[OF `parallel B D A L`] by blast
	have "D \<noteq> B" using NCdistinct[OF `\<not> col B D L`] by blast
	have "M \<noteq> A" using betweennotequal[OF `bet L M A`] by blast
	have "L \<noteq> M" using betweennotequal[OF `bet L M A`] by blast
	have "D = D" using equalityreflexiveE.
	have "col D B B" using collinear_b `B = B` by blast
	have "col D B B \<and> col L M A \<and> D \<noteq> B \<and> L \<noteq> M \<and> D \<noteq> B \<and> M \<noteq> A \<and> \<not> (meets D B L A) \<and> bet D c A \<and> col B M c" using `col D B B` `col L M A` `D \<noteq> B` `L \<noteq> M` `D \<noteq> B` `M \<noteq> A` `\<not> (meets D B L A)` `bet D c A \<and> col C B c \<and> \<not> col C B D` `col B M c` by blast
	have "bet B c M" using collinearbetween[OF `col D B B` `col L M A` `D \<noteq> B` `L \<noteq> A` `D \<noteq> B` `M \<noteq> A` `\<not> (meets D B L A)` `bet D c A` `col B M c`] .
	have "bet B c C" using n3_6b[OF `bet B c M` `bet B M C`] .
	have "\<not> col D B A" using parallelNC[OF `parallel D B L A`] by blast
	have "\<not> (B = c)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> c)"
		hence "B = c" by blast
		have "col D B c" using collinear_b `B = c` by blast
		have "col D c A" using collinear_b `bet D c A \<and> col C B c \<and> \<not> col C B D` by blast
		have "col c D B" using collinearorder[OF `col D B c`] by blast
		have "col c D A" using collinearorder[OF `col D c A`] by blast
		have "D \<noteq> c" using betweennotequal[OF `bet D c A`] by blast
		have "c \<noteq> D" using inequalitysymmetric[OF `D \<noteq> c`] .
		have "col D B A" using collinear4[OF `col c D B` `col c D A` `c \<noteq> D`] .
		show "False" using `col D B A` `\<not> col D B A` by blast
	qed
	hence "B \<noteq> c" by blast
	have "ray_on B c C" using ray4 `bet B c C` `B \<noteq> c` by blast
	have "ray_on B C c" using ray5[OF `ray_on B c C`] .
	have "\<not> col C B A" using NCorder[OF `\<not> col A B C`] by blast
	have "ang_eq C B A C B A" using equalanglesreflexive[OF `\<not> col C B A`] .
	have "A = A" using equalityreflexiveE.
	have "B \<noteq> A" using NCdistinct[OF `\<not> col A B C`] by blast
	have "ray_on B A A" using ray4 `A = A` `B \<noteq> A` by blast
	have "ang_eq C B A c B A" using equalangleshelper[OF `ang_eq C B A C B A` `ray_on B C c` `ray_on B A A`] .
	have "\<not> col C D B" using parallelNC[OF `parallel C E D B`] by blast
	have "\<not> col D B C" using NCorder[OF `\<not> col C B D`] by blast
	have "ang_eq D B C D B C" using equalanglesreflexive[OF `\<not> col D B C`] .
	have "B \<noteq> D" using inequalitysymmetric[OF `D \<noteq> B`] .
	have "ray_on B D D" using ray4 `D = D` `B \<noteq> D` by blast
	have "ang_eq D B C D B c" using equalangleshelper[OF `ang_eq D B C D B C` `ray_on B D D` `ray_on B C c`] .
	have "area_sum_eq D B C C B A D B A" using anglesum_b[OF `ang_eq D B C D B c` `ang_eq C B A c B A` `bet D c A`] .
	have "area_sum_eq F B A A B C F B C" using `area_sum_eq F B A A B C F B C` .
	have "area_sum_eq D B C C B A D B A" using `area_sum_eq D B C C B A D B A` .
	have "ang_eq F B A D B C" using Euclid4[OF `ang_right F B A` `ang_right D B C`] .
	have "ang_eq A B C C B A" using ABCequalsCBA[OF `\<not> col A B C`] .
	have "ang_eq F B C D B A" using angleaddition[OF `area_sum_eq F B A A B C F B C` `ang_eq F B A D B C` `ang_eq A B C C B A` `area_sum_eq D B C C B A D B A`] .
	have "ang_eq D B A F B C" using equalanglessymmetric[OF `ang_eq F B C D B A`] .
	have "\<not> (col C B F)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col C B F))"
hence "col C B F" by blast
		have "ang_right F B A" using `ang_right F B A` .
		have "col F B C" using collinearorder[OF `col C B F`] by blast
		have "ang_right C B A" using collinearright[OF `ang_right F B A` `col F B C` `C \<noteq> B`] .
		have "\<not> (ang_right C B A)" using n8_7[OF `ang_right B A C`] .
		show "False" using `\<not> (ang_right C B A)` `ang_right C B A` by blast
	qed
	hence "\<not> col C B F" by blast
	have "\<not> col F B C" using NCorder[OF `\<not> col C B F`] by blast
	have "ang_eq F B C C B F" using ABCequalsCBA[OF `\<not> col F B C`] .
	have "ang_eq D B A C B F" using equalanglestransitive[OF `ang_eq D B A F B C` `ang_eq F B C C B F`] .
	have "seg_eq A B B F" using square_f[OF `square A B F G`] by blast
	have "seg_eq A B F B" using congruenceflip[OF `seg_eq A B B F`] by blast
	have "seg_eq F B A B" using congruencesymmetric[OF `seg_eq A B F B`] .
	have "seg_eq B F B A" using congruenceflip[OF `seg_eq F B A B`] by blast
	have "seg_eq B A B F" using congruencesymmetric[OF `seg_eq B F B A`] .
	have "seg_eq B C D B" using square_f[OF `square B C E D`] by blast
	have "seg_eq D B B C" using congruencesymmetric[OF `seg_eq B C D B`] .
	have "seg_eq B D B C" using congruenceflip[OF `seg_eq D B B C`] by blast
	have "seg_eq D A C F \<and> ang_eq B D A B C F \<and> ang_eq B A D B F C" using Prop04[OF `seg_eq B D B C` `seg_eq B A B F` `ang_eq D B A C B F`] .
	have "seg_eq D A C F" using `seg_eq D A C F \<and> ang_eq B D A B C F \<and> ang_eq B A D B F C` by blast
	have "seg_eq A D F C" using congruenceflip[OF `seg_eq D A C F`] by blast
	have "ang_eq B A D B F C" using `seg_eq D A C F \<and> ang_eq B D A B C F \<and> ang_eq B A D B F C` by blast
	have "ang_eq B F C B A D" using equalanglessymmetric[OF `ang_eq B A D B F C`] .
	have "\<not> col B A D" using equalanglesNC[OF `ang_eq B F C B A D`] .
	have "\<not> col A B D" using NCorder[OF `\<not> col B A D`] by blast
	have "triangle A B D" using triangle_b[OF `\<not> col A B D`] .
	have "seg_eq A B F B \<and> seg_eq A D F C \<and> seg_eq B D B C \<and> triangle A B D" using `seg_eq A B F B` `seg_eq A D F C` `seg_eq B D B C` `triangle A B D` by blast
	have "tri_cong A B D F B C" using trianglecongruence_b[OF `seg_eq A B F B` `seg_eq B D B C` `seg_eq A D F C` `triangle A B D`] .
	have "tri_eq_area A B D F B C" using congruentequalE[OF `tri_cong A B D F B C`] .
	have "parallelogram B M L D" using `parallelogram B M L D` .
	have "parallel B M L D" using parallelogram_f[OF `parallelogram B M L D`] by blast
	have "parallel B D M L" using parallelogram_f[OF `parallelogram B M L D`] by blast
	have "parallel M L B D" using parallelsymmetric[OF `parallel B D M L`] .
	have "parallel M B D L" using parallelflip[OF `parallel B M L D`] by blast
	have "parallelogram M B D L" using parallelogram_b[OF `parallel M B D L` `parallel M L B D`] .
	have "col M L A" using collinearorder[OF `col L M A`] by blast
	have "tri_eq_area M B D A B D" using Prop41[OF `parallelogram M B D L` `col M L A`] .
	have "parallelogram A B F G" using squareparallelogram[OF `square A B F G`] .
	have "parallelogram B A G F" using PGflip[OF `parallelogram A B F G`] .
	have "col G A C" using collinear_b `bet G A C` by blast
	have "col A G C" using collinearorder[OF `col G A C`] by blast
	have "tri_eq_area A B F C B F" using Prop41[OF `parallelogram A B F G` `col A G C`] .
	have "tri_eq_area A B F F B C" using ETpermutationE[OF `tri_eq_area A B F C B F`] by blast
	have "tri_eq_area F B C A B D" using ETsymmetricE[OF `tri_eq_area A B D F B C`] .
	have "tri_eq_area A B F A B D" using ETtransitiveE[OF `tri_eq_area A B F F B C` `tri_eq_area F B C A B D`] .
	have "tri_eq_area A B D M B D" using ETsymmetricE[OF `tri_eq_area M B D A B D`] .
	have "tri_eq_area A B F M B D" using ETtransitiveE[OF `tri_eq_area A B F A B D` `tri_eq_area A B D M B D`] .
	have "tri_cong A B F F G A" using Prop34[OF `parallelogram B A G F`] by blast
	have "tri_eq_area A B F F G A" using congruentequalE[OF `tri_cong A B F F G A`] .
	have "parallelogram B M L D" using PGflip[OF `parallelogram M B D L`] .
	have "tri_cong M B D D L M" using Prop34[OF `parallelogram B M L D`] by blast
	have "tri_eq_area M B D D L M" using congruentequalE[OF `tri_cong M B D D L M`] .
	have "tri_eq_area F G A A B F" using ETsymmetricE[OF `tri_eq_area A B F F G A`] .
	have "tri_eq_area F G A A B D" using ETtransitiveE[OF `tri_eq_area F G A A B F` `tri_eq_area A B F A B D`] .
	have "tri_eq_area F G A M B D" using ETtransitiveE[OF `tri_eq_area F G A A B D` `tri_eq_area A B D M B D`] .
	have "tri_eq_area F G A D L M" using ETtransitiveE[OF `tri_eq_area F G A M B D` `tri_eq_area M B D D L M`] .
	have "tri_eq_area F G A D M L" using ETpermutationE[OF `tri_eq_area F G A D L M`] by blast
	have "tri_eq_area D M L F G A" using ETsymmetricE[OF `tri_eq_area F G A D M L`] .
	have "tri_eq_area D M L F A G" using ETpermutationE[OF `tri_eq_area D M L F G A`] by blast
	have "tri_eq_area F A G D M L" using ETsymmetricE[OF `tri_eq_area D M L F A G`] .
	have "tri_eq_area A B F D M B" using ETpermutationE[OF `tri_eq_area A B F M B D`] by blast
	have "tri_eq_area D M B A B F" using ETsymmetricE[OF `tri_eq_area A B F D M B`] .
	have "tri_eq_area D M B F A B" using ETpermutationE[OF `tri_eq_area D M B A B F`] by blast
	have "tri_eq_area F A B D M B" using ETsymmetricE[OF `tri_eq_area D M B F A B`] .
	obtain m where "midpoint A m F \<and> midpoint B m G" using diagonalsbisect[OF `parallelogram A B F G`]  by  blast
	have "midpoint A m F" using `midpoint A m F \<and> midpoint B m G` by blast
	have "midpoint B m G" using `midpoint A m F \<and> midpoint B m G` by blast
	have "bet A m F" using midpoint_f[OF `midpoint A m F`] by blast
	have "bet B m G" using midpoint_f[OF `midpoint B m G`] by blast
	have "bet F m A" using betweennesssymmetryE[OF `bet A m F`] .
	obtain n where "midpoint B n L \<and> midpoint M n D" using diagonalsbisect[OF `parallelogram B M L D`]  by  blast
	have "midpoint B n L" using `midpoint B n L \<and> midpoint M n D` by blast
	have "midpoint M n D" using `midpoint B n L \<and> midpoint M n D` by blast
	have "bet B n L" using midpoint_f[OF `midpoint B n L`] by blast
	have "bet M n D" using midpoint_f[OF `midpoint M n D`] by blast
	have "bet D n M" using betweennesssymmetryE[OF `bet M n D`] .
	have "col M n D" using collinear_b `bet M n D` by blast
	have "col D M n" using collinearorder[OF `col M n D`] by blast
	have "\<not> col B M D" using parallelNC[OF `parallel B M L D`] by blast
	have "\<not> col D M B" using NCorder[OF `\<not> col B M D`] by blast
	have "qua_eq_area F B A G D B M L" using paste3E `tri_eq_area F A B D M B` `tri_eq_area F A G D M L` `bet B m G` `bet F m A` `bet B n L` `bet D n M` by blast
	have "qua_eq_area F B A G B M L D" using EFpermutationE[OF `qua_eq_area F B A G D B M L`] by blast
	have "qua_eq_area B M L D F B A G" using EFsymmetricE[OF `qua_eq_area F B A G B M L D`] .
	have "qua_eq_area B M L D A B F G" using EFpermutationE[OF `qua_eq_area B M L D F B A G`] by blast
	have "qua_eq_area A B F G B M L D" using EFsymmetricE[OF `qua_eq_area B M L D A B F G`] .
	have "parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A \<and> qua_eq_area A B F G B M L D" using `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A` `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A` `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A` `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A` `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A` `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A` `qua_eq_area A B F G B M L D` by blast
	thus ?thesis by blast
qed

end