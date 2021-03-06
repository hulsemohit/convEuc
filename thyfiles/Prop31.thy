theory Prop31
	imports ABCequalsCBA Geometry NChelper NCorder Prop10 Prop27 betweennesspreserved betweennotequal collinearorder congruenceflip congruencesymmetric equalanglessymmetric equalanglestransitive inequalitysymmetric oppositesidesymmetric parallelflip pointreflectionisometry ray4
begin

theorem(in euclidean_geometry) Prop31:
	assumes 
		"bet B D C"
		"\<not> col B C A"
	shows "\<exists> E F M. bet E A F \<and> ang_eq F A D A D B \<and> ang_eq F A D B D A \<and> ang_eq D A F B D A \<and> ang_eq E A D A D C \<and> ang_eq E A D C D A \<and> ang_eq D A E C D A \<and> parallel E F B C \<and> seg_eq E A D C \<and> seg_eq A F B D \<and> seg_eq A M M D \<and> seg_eq E M M C \<and> seg_eq B M M F \<and> bet E M C \<and> bet B M F \<and> bet A M D"
proof -
	have "col B D C" using collinear_b `bet B D C` by blast
	have "\<not> (A = D)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> D)"
		hence "A = D" by blast
		have "col B A C" using `col B D C` `A = D` by blast
		have "col B C A" using collinearorder[OF `col B A C`] by blast
		show "False" using `col B C A` `\<not> col B C A` by blast
	qed
	hence "A \<noteq> D" by blast
	obtain M where "bet A M D \<and> seg_eq M A M D" using Prop10[OF `A \<noteq> D`]  by  blast
	have "bet A M D" using `bet A M D \<and> seg_eq M A M D` by blast
	have "seg_eq M A M D" using `bet A M D \<and> seg_eq M A M D` by blast
	have "seg_eq A M M D" using congruenceflip[OF `seg_eq M A M D`] by blast
	have "col C B D" using collinearorder[OF `col B D C`] by blast
	have "B = B" using equalityreflexiveE.
	have "col C B B" using collinear_b `B = B` by blast
	have "\<not> col C B A" using NCorder[OF `\<not> col B C A`] by blast
	have "B \<noteq> D" using betweennotequal[OF `bet B D C`] by blast
	have "\<not> col B D A" using NChelper[OF `\<not> col C B A` `col C B B` `col C B D` `B \<noteq> D`] .
	have "col B D C" using collinear_b `bet B D C` by blast
	have "D = D" using equalityreflexiveE.
	have "col B D D" using collinear_b `D = D` by blast
	have "D \<noteq> C" using betweennotequal[OF `bet B D C`] by blast
	have "C \<noteq> D" using inequalitysymmetric[OF `D \<noteq> C`] .
	have "\<not> col C D A" using NChelper[OF `\<not> col B D A` `col B D C` `col B D D` `C \<noteq> D`] .
	have "\<not> col A D C" using NCorder[OF `\<not> col C D A`] by blast
	have "col A M D" using collinear_b `bet A M D \<and> seg_eq M A M D` by blast
	have "col A D M" using collinearorder[OF `col A M D`] by blast
	have "A = A" using equalityreflexiveE.
	have "col A D A" using collinear_b `A = A` by blast
	have "A \<noteq> M" using betweennotequal[OF `bet A M D`] by blast
	have "\<not> col A M C" using NChelper[OF `\<not> col A D C` `col A D A` `col A D M` `A \<noteq> M`] .
	have "\<not> (C = M)"
	proof (rule ccontr)
		assume "\<not> (C \<noteq> M)"
		hence "C = M" by blast
		have "col A C M" using collinear_b `C = M` by blast
		have "col A M C" using collinearorder[OF `col A C M`] by blast
		show "False" using `col A M C` `\<not> col A M C` by blast
	qed
	hence "C \<noteq> M" by blast
	have "M \<noteq> C" using inequalitysymmetric[OF `C \<noteq> M`] .
	obtain E where "bet C M E \<and> seg_eq M E M C" using extensionE[OF `C \<noteq> M` `M \<noteq> C`]  by  blast
	have "bet C M E" using `bet C M E \<and> seg_eq M E M C` by blast
	have "seg_eq M E M C" using `bet C M E \<and> seg_eq M E M C` by blast
	have "seg_eq M C M E" using congruencesymmetric[OF `seg_eq M E M C`] .
	have "seg_eq C M M E" using congruenceflip[OF `seg_eq M C M E`] by blast
	have "midpoint C M E" using midpoint_b[OF `bet C M E` `seg_eq C M M E`] .
	have "A \<noteq> M" using betweennotequal[OF `bet A M D`] by blast
	have "\<not> col A D B" using NCorder[OF `\<not> col B D A`] by blast
	have "\<not> col A M B" using NChelper[OF `\<not> col A D B` `col A D A` `col A D M` `A \<noteq> M`] .
	have "\<not> (B = M)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> M)"
		hence "B = M" by blast
		have "col A B M" using collinear_b `B = M` by blast
		have "col A M B" using collinearorder[OF `col A B M`] by blast
		show "False" using `col A M B` `\<not> col A M B` by blast
	qed
	hence "B \<noteq> M" by blast
	have "M \<noteq> B" using inequalitysymmetric[OF `B \<noteq> M`] .
	obtain F where "bet B M F \<and> seg_eq M F M B" using extensionE[OF `B \<noteq> M` `M \<noteq> B`]  by  blast
	have "bet B M F" using `bet B M F \<and> seg_eq M F M B` by blast
	have "seg_eq M F M B" using `bet B M F \<and> seg_eq M F M B` by blast
	have "seg_eq M F B M" using congruenceflip[OF `seg_eq M F M B`] by blast
	have "seg_eq B M M F" using congruencesymmetric[OF `seg_eq M F B M`] .
	have "midpoint B M F" using midpoint_b[OF `bet B M F` `seg_eq B M M F`] .
	have "seg_eq M D M A" using congruencesymmetric[OF `seg_eq M A M D`] .
	have "bet D M A" using betweennesssymmetryE[OF `bet A M D`] .
	have "seg_eq D M M A" using congruenceflip[OF `seg_eq M D M A`] by blast
	have "midpoint D M A" using midpoint_b[OF `bet D M A` `seg_eq D M M A`] .
	have "seg_eq B D F A" using pointreflectionisometry[OF `midpoint B M F` `midpoint D M A`] .
	have "seg_eq D C A E" using pointreflectionisometry[OF `midpoint D M A` `midpoint C M E`] .
	have "seg_eq B C F E" using pointreflectionisometry[OF `midpoint B M F` `midpoint C M E`] .
	have "bet B D C" using `bet B D C` .
	have "bet F A E" using betweennesspreserved[OF `seg_eq B D F A` `seg_eq B C F E` `seg_eq D C A E` `bet B D C`] .
	have "bet E A F" using betweennesssymmetryE[OF `bet F A E`] .
	have "F = F" using equalityreflexiveE.
	have "A \<noteq> F" using betweennotequal[OF `bet E A F`] by blast
	have "ray_on A F F" using ray4 `F = F` `A \<noteq> F` by blast
	have "B = B" using equalityreflexiveE.
	have "B \<noteq> D" using betweennotequal[OF `bet B D C`] by blast
	have "D \<noteq> B" using inequalitysymmetric[OF `B \<noteq> D`] .
	have "ray_on D B B" using ray4 `B = B` `D \<noteq> B` by blast
	have "A = A" using equalityreflexiveE.
	have "D \<noteq> A" using betweennotequal[OF `bet D M A`] by blast
	have "ray_on D A A" using ray4 `A = A` `D \<noteq> A` by blast
	have "D = D" using equalityreflexiveE.
	have "A \<noteq> D" using inequalitysymmetric[OF `D \<noteq> A`] .
	have "ray_on A D D" using ray4 `D = D` `A \<noteq> D` by blast
	have "\<not> col B M A" using NCorder[OF `\<not> col A M B`] by blast
	have "col B M F" using collinear_b `bet B M F \<and> seg_eq M F M B` by blast
	have "M = M" using equalityreflexiveE.
	have "col B M M" using collinear_b `M = M` by blast
	have "M \<noteq> F" using betweennotequal[OF `bet B M F`] by blast
	have "F \<noteq> M" using inequalitysymmetric[OF `M \<noteq> F`] .
	have "\<not> col F M A" using NChelper[OF `\<not> col B M A` `col B M F` `col B M M` `F \<noteq> M`] .
	have "\<not> col A M F" using NCorder[OF `\<not> col F M A`] by blast
	have "col A M A" using collinear_b `A = A` by blast
	have "col A M D" using collinear_b `bet A M D \<and> seg_eq M A M D` by blast
	have "\<not> col A D F" using NChelper[OF `\<not> col A M F` `col A M A` `col A M D` `A \<noteq> D`] .
	have "\<not> col F A D" using NCorder[OF `\<not> col A D F`] by blast
	have "seg_eq D B A F" using congruenceflip[OF `seg_eq B D F A`] by blast
	have "midpoint B M F" using `midpoint B M F` .
	have "midpoint A M D" using midpoint_b[OF `bet A M D` `seg_eq A M M D`] .
	have "seg_eq B A F D" using pointreflectionisometry[OF `midpoint B M F` `midpoint A M D`] .
	have "seg_eq F D B A" using congruencesymmetric[OF `seg_eq B A F D`] .
	have "ray_on A F F" using `ray_on A F F` .
	have "ray_on A D D" using `ray_on A D D` .
	have "ray_on D B B" using `ray_on D B B` .
	have "ray_on D A A" using `ray_on D A A` .
	have "seg_eq A F D B" using congruencesymmetric[OF `seg_eq D B A F`] .
	have "seg_eq A D D A" using equalityreverseE.
	have "ang_eq F A D B D A" using equalangles_b[OF `ray_on A F F` `ray_on A D D` `ray_on D B B` `ray_on D A A` `seg_eq A F D B` `seg_eq A D D A` `seg_eq F D B A` `\<not> col F A D`] .
	have "\<not> col B D A" using NChelper[OF `\<not> col C B A` `col C B B` `col C B D` `B \<noteq> D`] .
	have "ang_eq B D A A D B" using ABCequalsCBA[OF `\<not> col B D A`] .
	have "ang_eq F A D A D B" using equalanglestransitive[OF `ang_eq F A D B D A` `ang_eq B D A A D B`] .
	have "ang_eq A D B F A D" using equalanglessymmetric[OF `ang_eq F A D A D B`] .
	have "\<not> col D A B" using NCorder[OF `\<not> col A D B`] by blast
	have "\<not> col F A D" using NCorder[OF `\<not> col A D F`] by blast
	have "ang_eq F A D D A F" using ABCequalsCBA[OF `\<not> col F A D`] .
	have "ang_eq A D B D A F" using equalanglestransitive[OF `ang_eq A D B F A D` `ang_eq F A D D A F`] .
	have "ang_eq D A F A D B" using equalanglessymmetric[OF `ang_eq A D B D A F`] .
	have "\<not> col A D B" using NCorder[OF `\<not> col B D A`] by blast
	have "ang_eq A D B B D A" using ABCequalsCBA[OF `\<not> col A D B`] .
	have "ang_eq D A F B D A" using equalanglestransitive[OF `ang_eq D A F A D B` `ang_eq A D B B D A`] .
	have "oppo_side B A D F" using oppositeside_b[OF `bet B M F` `col A D M` `\<not> col A D B`] .
	have "oppo_side F A D B" using oppositesidesymmetric[OF `oppo_side B A D F`] .
	have "bet F A E" using `bet F A E` .
	have "bet C D B" using betweennesssymmetryE[OF `bet B D C`] .
	have "parallel F E C B" using Prop27[OF `bet F A E` `bet C D B` `ang_eq F A D A D B` `oppo_side F A D B`] .
	have "parallel E F B C" using parallelflip[OF `parallel F E C B`] by blast
	have "seg_eq D C E A" using congruenceflip[OF `seg_eq D C A E`] by blast
	have "seg_eq E A D C" using congruencesymmetric[OF `seg_eq D C E A`] .
	have "seg_eq B D A F" using congruenceflip[OF `seg_eq B D F A`] by blast
	have "seg_eq A F B D" using congruencesymmetric[OF `seg_eq B D A F`] .
	have "seg_eq M C E M" using congruenceflip[OF `seg_eq C M M E`] by blast
	have "seg_eq E M M C" using congruencesymmetric[OF `seg_eq M C E M`] .
	have "E \<noteq> A" using betweennotequal[OF `bet E A F`] by blast
	have "A \<noteq> E" using inequalitysymmetric[OF `E \<noteq> A`] .
	have "E = E" using equalityreflexiveE.
	have "ray_on A E E" using ray4 `E = E` `A \<noteq> E` by blast
	have "D \<noteq> C" using betweennotequal[OF `bet B D C`] by blast
	have "C = C" using equalityreflexiveE.
	have "ray_on D C C" using ray4 `C = C` `D \<noteq> C` by blast
	have "seg_eq E M M C" using congruenceflip[OF `seg_eq M E M C`] by blast
	have "bet E M C" using betweennesssymmetryE[OF `bet C M E`] .
	have "midpoint E M C" using midpoint_b[OF `bet E M C` `seg_eq E M M C`] .
	have "midpoint D M A" using `midpoint D M A` .
	have "seg_eq E D C A" using pointreflectionisometry[OF `midpoint E M C` `midpoint D M A`] .
	have "seg_eq A E D C" using pointreflectionisometry[OF `midpoint A M D` `midpoint E M C`] .
	have "col E A F" using collinear_b `bet E A F` by blast
	have "col F A E" using collinearorder[OF `col E A F`] by blast
	have "\<not> col F A D" using `\<not> col F A D` .
	have "col F A A" using collinear_b `A = A` by blast
	have "\<not> col E A D" using NChelper[OF `\<not> col F A D` `col F A E` `col F A A` `E \<noteq> A`] .
	have "ray_on A E E" using `ray_on A E E` .
	have "ray_on A D D" using `ray_on A D D` .
	have "ray_on D A A" using `ray_on D A A` .
	have "seg_eq A D D A" using `seg_eq A D D A` .
	have "seg_eq A E D C" using `seg_eq A E D C` .
	have "seg_eq E D C A" using `seg_eq E D C A` .
	have "ang_eq E A D C D A" using equalangles_b[OF `ray_on A E E` `ray_on A D D` `ray_on D C C` `ray_on D A A` `seg_eq A E D C` `seg_eq A D D A` `seg_eq E D C A` `\<not> col E A D`] .
	have "\<not> col C D A" using NCorder[OF `\<not> col A D C`] by blast
	have "ang_eq C D A A D C" using ABCequalsCBA[OF `\<not> col C D A`] .
	have "ang_eq E A D A D C" using equalanglestransitive[OF `ang_eq E A D C D A` `ang_eq C D A A D C`] .
	have "\<not> col D A E" using NCorder[OF `\<not> col E A D`] by blast
	have "ang_eq D A E E A D" using ABCequalsCBA[OF `\<not> col D A E`] .
	have "ang_eq D A E C D A" using equalanglestransitive[OF `ang_eq D A E E A D` `ang_eq E A D C D A`] .
	have "bet E A F \<and> ang_eq F A D A D B \<and> ang_eq F A D B D A \<and> ang_eq D A F B D A \<and> ang_eq E A D A D C \<and> ang_eq E A D C D A \<and> ang_eq D A E C D A \<and> parallel E F B C \<and> seg_eq E A D C \<and> seg_eq A F B D \<and> seg_eq A M M D \<and> seg_eq E M M C \<and> seg_eq B M M F \<and> bet E M C \<and> bet B M F \<and> bet A M D" using `bet E A F` `ang_eq F A D A D B` `ang_eq F A D B D A` `ang_eq D A F B D A` `ang_eq E A D A D C` `ang_eq E A D C D A` `ang_eq D A E C D A` `parallel E F B C` `seg_eq E A D C` `seg_eq A F B D` `seg_eq A M M D` `seg_eq E M M C` `seg_eq B M M F` `bet E M C` `bet B M F \<and> seg_eq M F M B` `bet A M D \<and> seg_eq M A M D` by blast
	thus ?thesis by blast
qed

end