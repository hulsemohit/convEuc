theory Prop32
	imports Axioms Definitions Theorems
begin

theorem Prop32:
	assumes: `axioms`
		"triangle A B C"
		"bet B C D"
	shows: "area_sum_eq C A B A B C A C D"
proof -
	have "\<not> col A B C" using triangle_f[OF `axioms` `triangle A B C`] .
	have "B \<noteq> A" using NCdistinct[OF `axioms` `\<not> col A B C`] by blast
	have "A \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> A`] .
	obtain F where "bet B A F \<and> seg_eq A F B A" using extensionE[OF `axioms` `B \<noteq> A` `B \<noteq> A`] by blast
	have "bet B A F" using `bet B A F \<and> seg_eq A F B A` by blast
	have "col B A F" using collinear_b `axioms` `bet B A F \<and> seg_eq A F B A` by blast
	have "col A B F" using collinearorder[OF `axioms` `col B A F`] by blast
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "col A B B" using collinear_b `axioms` `B = B` by blast
	have "B \<noteq> F" using betweennotequal[OF `axioms` `bet B A F`] by blast
	have "F \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> F`] .
	have "\<not> col F B C" using NChelper[OF `axioms` `\<not> col A B C` `col A B F` `col A B B` `F \<noteq> B`] .
	have "bet F A B" using betweennesssymmetryE[OF `axioms` `bet B A F`] .
	obtain E H S where "bet E C H \<and> ang_eq E C A C A B \<and> parallel E H F B \<and> bet E S B \<and> bet C S A" using Prop31short[OF `axioms` `bet F A B` `\<not> col F B C`] by blast
	have "B \<noteq> C" using betweennotequal[OF `axioms` `bet B C D`] by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> C`] .
	obtain G where "bet C B G \<and> seg_eq B G C B" using extensionE[OF `axioms` `C \<noteq> B` `C \<noteq> B`] by blast
	have "C \<noteq> A" using NCdistinct[OF `axioms` `\<not> col A B C`] by blast
	obtain J where "bet C A J \<and> seg_eq A J C A" using extensionE[OF `axioms` `C \<noteq> A` `C \<noteq> A`] by blast
	have "A \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> A`] .
	obtain K where "bet A C K \<and> seg_eq C K A C" using extensionE[OF `axioms` `A \<noteq> C` `A \<noteq> C`] by blast
	have "bet A C K" using `bet A C K \<and> seg_eq C K A C` by blast
	obtain M where "bet A B M \<and> seg_eq B M A B" using extensionE[OF `axioms` `A \<noteq> B` `A \<noteq> B`] by blast
	have "bet A B M" using `bet A B M \<and> seg_eq B M A B` by blast
	have "parallel E H F B" using `bet E C H \<and> ang_eq E C A C A B \<and> parallel E H F B \<and> bet E S B \<and> bet C S A` by blast
	have "col F B A" using collinearorder[OF `axioms` `col A B F`] by blast
	have "parallel E H A B" using collinearparallel[OF `axioms` `parallel E H F B` `col F B A` `A \<noteq> B`] .
	have "bet E C H" using `bet E C H \<and> ang_eq E C A C A B \<and> parallel E H F B \<and> bet E S B \<and> bet C S A` by blast
	have "bet K C A" using betweennesssymmetryE[OF `axioms` `bet A C K`] .
	have "bet E S B" using `bet E C H \<and> ang_eq E C A C A B \<and> parallel E H F B \<and> bet E S B \<and> bet C S A` by blast
	have "bet C S A" using `bet E C H \<and> ang_eq E C A C A B \<and> parallel E H F B \<and> bet E S B \<and> bet C S A` by blast
	have "col C S A" using collinear_b `axioms` `bet E C H \<and> ang_eq E C A C A B \<and> parallel E H F B \<and> bet E S B \<and> bet C S A` by blast
	have "col C A S" using collinearorder[OF `axioms` `col C S A`] by blast
	have "\<not> col A C B" using NCorder[OF `axioms` `\<not> col A B C`] by blast
	have "col A C S" using collinearorder[OF `axioms` `col C A S`] by blast
	have "C \<noteq> S" using betweennotequal[OF `axioms` `bet C S A`] by blast
	have "S \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> S`] .
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "col A C C" using collinear_b `axioms` `C = C` by blast
	have "\<not> col S C B" using NChelper[OF `axioms` `\<not> col A C B` `col A C S` `col A C C` `S \<noteq> C`] .
	have "\<not> col B S C" using NCorder[OF `axioms` `\<not> col S C B`] by blast
	have "col E S B" using collinear_b `axioms` `bet E C H \<and> ang_eq E C A C A B \<and> parallel E H F B \<and> bet E S B \<and> bet C S A` by blast
	have "col B S E" using collinearorder[OF `axioms` `col E S B`] by blast
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "col B S B" using collinear_b `axioms` `B = B` by blast
	have "bet B S E" using betweennesssymmetryE[OF `axioms` `bet E S B`] .
	have "B \<noteq> E" using betweennotequal[OF `axioms` `bet B S E`] by blast
	have "\<not> col B E C" using NChelper[OF `axioms` `\<not> col B S C` `col B S B` `col B S E` `B \<noteq> E`] .
	have "col B E S" using collinearorder[OF `axioms` `col B S E`] by blast
	have "E = E" using equalityreflexiveE[OF `axioms`] .
	have "col B E E" using collinear_b `axioms` `E = E` by blast
	have "S \<noteq> E" using betweennotequal[OF `axioms` `bet B S E`] by blast
	have "\<not> col S E C" using NChelper[OF `axioms` `\<not> col B E C` `col B E S` `col B E E` `S \<noteq> E`] .
	have "\<not> col S C E" using NCorder[OF `axioms` `\<not> col S E C`] by blast
	have "col S C C" using collinear_b `axioms` `C = C` by blast
	have "col C S A" using collinear_b `axioms` `bet E C H \<and> ang_eq E C A C A B \<and> parallel E H F B \<and> bet E S B \<and> bet C S A` by blast
	have "col S C A" using collinearorder[OF `axioms` `col A C S`] by blast
	have "C \<noteq> A" using betweennotequal `axioms` `bet C A J \<and> seg_eq A J C A` by blast
	have "\<not> col C A E" using NChelper[OF `axioms` `\<not> col S C E` `col S C C` `col S C A` `C \<noteq> A`] .
	have "col A B M" using collinear_b `axioms` `bet A B M \<and> seg_eq B M A B` by blast
	have "col B A M" using collinearorder[OF `axioms` `col A B M`] by blast
	have "parallel E H B A" using parallelflip[OF `axioms` `parallel E H A B`] by blast
	have "A \<noteq> M" using betweennotequal[OF `axioms` `bet A B M`] by blast
	have "M \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> M`] .
	have "parallel E H M A" using collinearparallel[OF `axioms` `parallel E H B A` `col B A M` `M \<noteq> A`] .
	have "bet H C E" using betweennesssymmetryE[OF `axioms` `bet E C H`] .
	have "bet M B A" using betweennesssymmetryE[OF `axioms` `bet A B M`] .
	have "bet F A B" using betweennesssymmetryE[OF `axioms` `bet B A F`] .
	have "bet D C B" using betweennesssymmetryE[OF `axioms` `bet B C D`] .
	have "\<not> col B C A" using NCorder[OF `axioms` `\<not> col A B C`] by blast
	have "bet C S A" using `bet C S A` .
	have "bet B S E" using `bet B S E` .
	have "\<not> col A C B" using NCorder[OF `axioms` `\<not> col A B C`] by blast
	have "A = A" using equalityreflexiveE[OF `axioms`] .
	have "B \<noteq> E" using betweennotequal[OF `axioms` `bet B S E`] by blast
	have "bet E C H" using betweennesssymmetryE[OF `axioms` `bet H C E`] .
	have "bet A S C" using betweennesssymmetryE[OF `axioms` `bet C S A`] .
	have "\<not> col C A E" using `\<not> col C A E` .
	have "\<not> col C E A" using NCorder[OF `axioms` `\<not> col C A E`] by blast
	have "col C E H" using collinear_b `axioms` `bet E C H \<and> ang_eq E C A C A B \<and> parallel E H F B \<and> bet E S B \<and> bet C S A` by blast
	have "col C E E" using collinear_b `axioms` `E = E` by blast
	have "E \<noteq> H" using betweennotequal[OF `axioms` `bet E C H`] by blast
	have "H \<noteq> E" using inequalitysymmetric[OF `axioms` `E \<noteq> H`] .
	have "\<not> col H E A" using NChelper[OF `axioms` `\<not> col C E A` `col C E H` `col C E E` `H \<noteq> E`] .
	have "\<not> col E H A" using NCorder[OF `axioms` `\<not> col H E A`] by blast
	obtain Q where "bet A Q H \<and> bet E S Q" using Pasch-outerE[OF `axioms` `bet A S C` `bet E C H` `\<not> col E H A`] by blast
	have "bet A Q H" using `bet A Q H \<and> bet E S Q` by blast
	have "bet E S Q" using `bet A Q H \<and> bet E S Q` by blast
	have "col E S Q" using collinear_b `axioms` `bet A Q H \<and> bet E S Q` by blast
	have "col S E B" using collinearorder[OF `axioms` `col B E S`] by blast
	have "col S E Q" using collinearorder[OF `axioms` `col E S Q`] by blast
	have "S \<noteq> E" using `S \<noteq> E` .
	have "col E B Q" using collinear4[OF `axioms` `col S E B` `col S E Q` `S \<noteq> E`] .
	have "col B E Q" using collinearorder[OF `axioms` `col E B Q`] by blast
	have "H \<noteq> E" using betweennotequal[OF `axioms` `bet H C E`] by blast
	have "C \<noteq> E" using betweennotequal[OF `axioms` `bet H C E`] by blast
	obtain L where "bet H E L \<and> seg_eq E L C E" using extensionE[OF `axioms` `H \<noteq> E` `C \<noteq> E`] by blast
	have "bet H E L" using `bet H E L \<and> seg_eq E L C E` by blast
	have "bet L E H" using betweennesssymmetryE[OF `axioms` `bet H E L`] .
	have "col L E H" using collinear_b `axioms` `bet L E H` by blast
	have "L \<noteq> H" using betweennotequal[OF `axioms` `bet L E H`] by blast
	have "E \<noteq> H" using betweennotequal[OF `axioms` `bet E C H`] by blast
	have "bet A B M" using `bet A B M` .
	have "col A B M" using collinear_b `axioms` `bet A B M \<and> seg_eq B M A B` by blast
	have "A \<noteq> M" using betweennotequal[OF `axioms` `bet A B M`] by blast
	have "A \<noteq> B" using betweennotequal[OF `axioms` `bet A B M`] by blast
	have "\<not> (meets A M L H)"
	proof (rule ccontr)
		assume "meets A M L H"
		obtain c where "A \<noteq> M \<and> L \<noteq> H \<and> col A M c \<and> col L H c" using meet_f[OF `axioms` `meets A M L H`] by blast
		have "col A M c" using `A \<noteq> M \<and> L \<noteq> H \<and> col A M c \<and> col L H c` by blast
		have "col L H c" using `A \<noteq> M \<and> L \<noteq> H \<and> col A M c \<and> col L H c` by blast
		have "col H E L" using collinear_b `axioms` `bet H E L \<and> seg_eq E L C E` by blast
		have "col L H E" using collinearorder[OF `axioms` `col H E L`] by blast
		have "H \<noteq> L" using betweennotequal[OF `axioms` `bet H E L`] by blast
		have "L \<noteq> H" using inequalitysymmetric[OF `axioms` `H \<noteq> L`] .
		have "col H c E" using collinear4[OF `axioms` `col L H c` `col L H E` `L \<noteq> H`] .
		have "col E H c" using collinearorder[OF `axioms` `col H c E`] by blast
		have "col A B M" using collinear_b `axioms` `bet A B M \<and> seg_eq B M A B` by blast
		have "col M A B" using collinearorder[OF `axioms` `col A B M`] by blast
		have "col M A c" using collinearorder[OF `axioms` `col A M c`] by blast
		have "A \<noteq> M" using betweennotequal[OF `axioms` `bet A B M`] by blast
		have "M \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> M`] .
		have "col A B c" using collinear4[OF `axioms` `col M A B` `col M A c` `M \<noteq> A`] .
		have "col B A F" using collinear_b `axioms` `bet B A F \<and> seg_eq A F B A` by blast
		have "col A B F" using collinearorder[OF `axioms` `col B A F`] by blast
		have "col B c F" using collinear4[OF `axioms` `col A B c` `col A B F` `A \<noteq> B`] .
		have "col F B c" using collinearorder[OF `axioms` `col B c F`] by blast
		have "E \<noteq> H \<and> F \<noteq> B \<and> col E H c \<and> col F B c" using `E \<noteq> H` `F \<noteq> B` `col E H c` `col F B c` by blast
		have "meets E H F B" using meet_b[OF `axioms` `E \<noteq> H` `F \<noteq> B` `col E H c` `col F B c`] .
		have "\<not> (meets E H F B)" using parallel_f[OF `axioms` `parallel E H F B`] by blast
		show "False" using `\<not> (meets E H F B)` `meets E H F B` by blast
	qed
	hence "\<not> (meets A M L H)" by blast
	have "bet B Q E" using collinearbetween[OF `axioms` `col A B M` `col L E H` `A \<noteq> M` `L \<noteq> H` `A \<noteq> B` `E \<noteq> H` `\<not> (meets A M L H)` `bet A Q H` `col B E Q`] .
	have "\<not> col A H E" using NCorder[OF `axioms` `\<not> col E H A`] by blast
	have "col A Q H" using collinear_b `axioms` `bet A Q H \<and> bet E S Q` by blast
	have "col A H Q" using collinearorder[OF `axioms` `col A Q H`] by blast
	have "H = H" using equalityreflexiveE[OF `axioms`] .
	have "col A H H" using collinear_b `axioms` `H = H` by blast
	have "Q \<noteq> H" using betweennotequal[OF `axioms` `bet A Q H`] by blast
	have "\<not> col Q H E" using NChelper[OF `axioms` `\<not> col A H E` `col A H Q` `col A H H` `Q \<noteq> H`] .
	have "\<not> col Q E H" using NCorder[OF `axioms` `\<not> col Q H E`] by blast
	have "E = E" using equalityreflexiveE[OF `axioms`] .
	have "col Q E E" using collinear_b `axioms` `E = E` by blast
	have "col Q E B" using collinearorder[OF `axioms` `col B E Q`] by blast
	have "\<not> col B E H" using NChelper[OF `axioms` `\<not> col Q E H` `col Q E B` `col Q E E` `B \<noteq> E`] .
	obtain T where "bet B T C \<and> bet H T Q" using Pasch-innerE[OF `axioms` `bet B Q E` `bet H C E` `\<not> col B E H`] by blast
	have "bet B T C" using `bet B T C \<and> bet H T Q` by blast
	have "bet H T Q" using `bet B T C \<and> bet H T Q` by blast
	have "bet Q T H" using betweennesssymmetryE[OF `axioms` `bet H T Q`] .
	have "bet A Q H" using `bet A Q H` .
	have "bet A T H" using n3_5b[OF `axioms` `bet A Q H` `bet Q T H`] .
	have "col B T C" using collinear_b `axioms` `bet B T C \<and> bet H T Q` by blast
	have "col C B T" using collinearorder[OF `axioms` `col B T C`] by blast
	have "\<not> col C B A" using NCorder[OF `axioms` `\<not> col A B C`] by blast
	have "oppo_side A C B H" using oppositeside_b[OF `axioms` `bet A T H` `col C B T` `\<not> col C B A`] .
	have "oppo_side H C B A" using oppositesidesymmetric[OF `axioms` `oppo_side A C B H`] .
	have "parallel H E M A" using parallelflip[OF `axioms` `parallel E H M A`] by blast
	have "bet H C E" using `bet H C E` .
	have "bet M B A" using `bet M B A` .
	have "ang_eq E C A C A B" using `bet E C H \<and> ang_eq E C A C A B \<and> parallel E H F B \<and> bet E S B \<and> bet C S A` by blast
	have "ang_eq A C E B A C" using equalanglesflip[OF `axioms` `ang_eq E C A C A B`] .
	have "ang_eq H C B C B A \<and> ang_eq D C E C B A \<and> ang_suppl E C B C B A" using Prop29[OF `axioms` `parallel H E M A` `bet H C E` `bet M B A` `bet D C B` `oppo_side H C B A`] .
	have "ang_eq D C E C B A" using `ang_eq H C B C B A \<and> ang_eq D C E C B A \<and> ang_suppl E C B C B A` by blast
	have "ang_eq C B A A B C" using ABCequalsCBA[OF `axioms` `\<not> col C B A`] .
	have "ang_eq D C E A B C" using equalanglestransitive[OF `axioms` `ang_eq D C E C B A` `ang_eq C B A A B C`] .
	have "bet B T C" using `bet B T C` .
	have "bet B C D" using `bet B C D` .
	have "bet T C D" using n3_6a[OF `axioms` `bet B T C` `bet B C D`] .
	have "T \<noteq> D" using betweennotequal[OF `axioms` `bet T C D`] by blast
	have "\<not> col B C A" using NCorder[OF `axioms` `\<not> col A B C`] by blast
	have "col B C T" using collinearorder[OF `axioms` `col B T C`] by blast
	have "col B C D" using collinear_b `axioms` `bet B C D` by blast
	have "\<not> col T D A" using NChelper[OF `axioms` `\<not> col B C A` `col B C T` `col B C D` `T \<noteq> D`] .
	have "\<not> col A T D" using NCorder[OF `axioms` `\<not> col T D A`] by blast
	have "col A T A" using collinear_b `axioms` `A = A` by blast
	have "col A T H" using collinear_b `axioms` `bet A T H` by blast
	have "A \<noteq> H" using betweennotequal[OF `axioms` `bet A Q H`] by blast
	have "\<not> col A H D" using NChelper[OF `axioms` `\<not> col A T D` `col A T A` `col A T H` `A \<noteq> H`] .
	have "\<not> col H A D" using NCorder[OF `axioms` `\<not> col A H D`] by blast
	have "bet H T A" using betweennesssymmetryE[OF `axioms` `bet A T H`] .
	have "bet D C T" using betweennesssymmetryE[OF `axioms` `bet T C D`] .
	obtain R where "bet D R A \<and> bet H C R" using Pasch-outerE[OF `axioms` `bet D C T` `bet H T A` `\<not> col H A D`] by blast
	have "bet D R A" using `bet D R A \<and> bet H C R` by blast
	have "bet H C R" using `bet D R A \<and> bet H C R` by blast
	have "ray_on C E R" using ray_b[OF `axioms` `bet H C R` `bet H C E`] .
	have "ray_on C A A" using ray4 `axioms` `A = A` `C \<noteq> A` by blast
	have "C \<noteq> D" using betweennotequal[OF `axioms` `bet B C D`] by blast
	have "D = D" using equalityreflexiveE[OF `axioms`] .
	have "bet A R D" using betweennesssymmetryE[OF `axioms` `bet D R A`] .
	have "ang_eq B A C A C E" using equalanglessymmetric[OF `axioms` `ang_eq A C E B A C`] .
	have "ang_eq B A C A C R" using equalangleshelper[OF `axioms` `ang_eq B A C A C E` `ray_on C A A` `ray_on C E R`] .
	have "\<not> col C A B" using NCorder[OF `axioms` `\<not> col A B C`] by blast
	have "ang_eq C A B B A C" using ABCequalsCBA[OF `axioms` `\<not> col C A B`] .
	have "ang_eq C A B A C R" using equalanglestransitive[OF `axioms` `ang_eq C A B B A C` `ang_eq B A C A C R`] .
	have "bet A R D" using `bet A R D` .
	have "ray_on C D D" using ray4 `axioms` `D = D` `C \<noteq> D` by blast
	have "ang_eq A B C D C E" using equalanglessymmetric[OF `axioms` `ang_eq D C E A B C`] .
	have "ang_eq A B C D C R" using equalangleshelper[OF `axioms` `ang_eq A B C D C E` `ray_on C D D` `ray_on C E R`] .
	have "\<not> col A D H" using NCorder[OF `axioms` `\<not> col A H D`] by blast
	have "col D R A" using collinear_b `axioms` `bet D R A \<and> bet H C R` by blast
	have "col A D R" using collinearorder[OF `axioms` `col D R A`] by blast
	have "D = D" using equalityreflexiveE[OF `axioms`] .
	have "col A D D" using collinear_b `axioms` `D = D` by blast
	have "D \<noteq> R" using betweennotequal[OF `axioms` `bet D R A`] by blast
	have "R \<noteq> D" using inequalitysymmetric[OF `axioms` `D \<noteq> R`] .
	have "\<not> col R D H" using NChelper[OF `axioms` `\<not> col A D H` `col A D R` `col A D D` `R \<noteq> D`] .
	have "\<not> col R H D" using NCorder[OF `axioms` `\<not> col R D H`] by blast
	have "col H C R" using collinear_b `axioms` `bet D R A \<and> bet H C R` by blast
	have "col R H C" using collinearorder[OF `axioms` `col H C R`] by blast
	have "R = R" using equalityreflexiveE[OF `axioms`] .
	have "col R H R" using collinear_b `axioms` `R = R` by blast
	have "C \<noteq> R" using betweennotequal[OF `axioms` `bet H C R`] by blast
	have "R \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> R`] .
	have "\<not> col R C D" using NChelper[OF `axioms` `\<not> col R H D` `col R H R` `col R H C` `R \<noteq> C`] .
	have "\<not> col D C R" using NCorder[OF `axioms` `\<not> col R C D`] by blast
	have "ang_eq D C R R C D" using ABCequalsCBA[OF `axioms` `\<not> col D C R`] .
	have "ang_eq A B C R C D" using equalanglestransitive[OF `axioms` `ang_eq A B C D C R` `ang_eq D C R R C D`] .
	have "ang_eq C A B A C R \<and> ang_eq A B C R C D \<and> bet A R D" using `ang_eq C A B A C R` `ang_eq A B C R C D` `bet A R D` by blast
	have "area_sum_eq C A B A B C A C D" using anglesum_b[OF `axioms` `ang_eq C A B A C R` `ang_eq A B C R C D` `bet A R D`] .
	thus ?thesis by blast
qed

end