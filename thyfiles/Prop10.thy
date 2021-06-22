theory Prop10
	imports Axioms Definitions Theorems
begin

theorem Prop10:
	assumes: `axioms`
		"A \<noteq> B"
	shows: "\<exists> M. bet A M B \<and> seg_eq M A M B"
proof -
	obtain C where "equilateral A B C \<and> triangle A B C" using Prop01[OF `axioms` `A \<noteq> B`] by blast
	have "equilateral A B C" using `equilateral A B C \<and> triangle A B C` by blast
	have "triangle A B C" using `equilateral A B C \<and> triangle A B C` by blast
	have "\<not> col A B C" using triangle_f[OF `axioms` `triangle A B C`] .
	have "seg_eq A B B C \<and> seg_eq B C C A" using equilateral_f[OF `axioms` `equilateral A B C`] .
	have "seg_eq B C C A" using `seg_eq A B B C \<and> seg_eq B C C A` by blast
	have "seg_eq A C C B" using doublereverse[OF `axioms` `seg_eq B C C A`] by blast
	have "seg_eq A C B C" using congruenceflip[OF `axioms` `seg_eq A C C B`] by blast
	have "\<not> (C = B)"
	proof (rule ccontr)
		assume "C = B"
		have "col A C B" using collinear_b `axioms` `C = B` by blast
		have "col A B C" using collinearorder[OF `axioms` `col A C B`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "C \<noteq> B" by blast
	obtain D where "bet C B D \<and> seg_eq B D A B" using extensionE[OF `axioms` `C \<noteq> B` `A \<noteq> B`] by blast
	have "seg_eq B D A B" using `bet C B D \<and> seg_eq B D A B` by blast
	have "\<not> (C = A)"
	proof (rule ccontr)
		assume "C = A"
		have "col B C A" using collinear_b `axioms` `C = A` by blast
		have "col A B C" using collinearorder[OF `axioms` `col B C A`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "C \<noteq> A" by blast
	obtain E where "bet C A E \<and> seg_eq A E A B" using extensionE[OF `axioms` `C \<noteq> A` `A \<noteq> B`] by blast
	have "seg_eq A E A B" using `bet C A E \<and> seg_eq A E A B` by blast
	have "bet C B D" using `bet C B D \<and> seg_eq B D A B` by blast
	have "bet C A E" using `bet C A E \<and> seg_eq A E A B` by blast
	have "bet D B C" using betweennesssymmetryE[OF `axioms` `bet C B D`] .
	have "bet E A C" using betweennesssymmetryE[OF `axioms` `bet C A E`] .
	have "\<not> (col D C E)"
	proof (rule ccontr)
		assume "col D C E"
		have "col C A E" using collinear_b `axioms` `bet C A E \<and> seg_eq A E A B` by blast
		have "col C B D" using collinear_b `axioms` `bet C B D \<and> seg_eq B D A B` by blast
		have "col E C D" using collinearorder[OF `axioms` `col D C E`] by blast
		have "col E C A" using collinearorder[OF `axioms` `col C A E`] by blast
		have "C \<noteq> E" using betweennotequal[OF `axioms` `bet C A E`] by blast
		have "E \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> E`] .
		have "col C D A" using collinear4[OF `axioms` `col E C D` `col E C A` `E \<noteq> C`] .
		have "col D C B" using collinearorder[OF `axioms` `col C B D`] by blast
		have "col D C A" using collinearorder[OF `axioms` `col C D A`] by blast
		have "C \<noteq> D" using betweennotequal[OF `axioms` `bet C B D`] by blast
		have "D \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> D`] .
		have "col C B A" using collinear4[OF `axioms` `col D C B` `col D C A` `D \<noteq> C`] .
		have "col A B C" using collinearorder[OF `axioms` `col C B A`] by blast
		have "\<not> col A B C" using `\<not> col A B C` .
		show "False" using `\<not> col A B C` `col A B C` by blast
	qed
	hence "\<not> col D C E" by blast
	obtain F where "bet D F A \<and> bet E F B" using Pasch-innerE[OF `axioms` `bet D B C` `bet E A C` `\<not> col D C E`] by blast
	have "bet D F A" using `bet D F A \<and> bet E F B` by blast
	have "bet E F B" using `bet D F A \<and> bet E F B` by blast
	have "bet B F E" using betweennesssymmetryE[OF `axioms` `bet E F B`] .
	have "bet A F D" using betweennesssymmetryE[OF `axioms` `bet D F A`] .
	have "bet C B D" using `bet C B D` .
	have "C \<noteq> D" using betweennotequal[OF `axioms` `bet C B D`] by blast
	have "D \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> D`] .
	have "\<not> (col A D C)"
	proof (rule ccontr)
		assume "col A D C"
		have "col C B D" using collinear_b `axioms` `bet C B D \<and> seg_eq B D A B` by blast
		have "col D C A" using collinearorder[OF `axioms` `col A D C`] by blast
		have "col D C B" using collinearorder[OF `axioms` `col C B D`] by blast
		have "col C A B" using collinear4[OF `axioms` `col D C A` `col D C B` `D \<noteq> C`] .
		have "col A B C" using collinearorder[OF `axioms` `col C A B`] by blast
		have "\<not> col A B C" using `\<not> col A B C` .
		show "False" using `\<not> col A B C` `col A B C` by blast
	qed
	hence "\<not> col A D C" by blast
	obtain M where "bet A M B \<and> bet C M F" using Pasch-innerE[OF `axioms` `bet A F D` `bet C B D` `\<not> col A D C`] by blast
	have "bet A M B" using `bet A M B \<and> bet C M F` by blast
	have "bet C M F" using `bet A M B \<and> bet C M F` by blast
	have "seg_eq C A C B" using congruenceflip[OF `axioms` `seg_eq A C B C`] by blast
	have "seg_eq A B A E" using congruencesymmetric[OF `axioms` `seg_eq A E A B`] .
	have "seg_eq B D A E" using congruencetransitive[OF `axioms` `seg_eq B D A B` `seg_eq A B A E`] .
	have "seg_eq A E B D" using congruencesymmetric[OF `axioms` `seg_eq B D A E`] .
	have "seg_eq A B B A" using equalityreverseE[OF `axioms`] by blast
	have "bet C A E" using `bet C A E` .
	have "bet C B D" using `bet C B D` .
	have "seg_eq C B C A" using congruencesymmetric[OF `axioms` `seg_eq C A C B`] .
	have "seg_eq B E A D" using 5-lineE[OF `axioms` `seg_eq A E B D` `seg_eq C B C A` `seg_eq A B B A` `bet C A E` `bet C B D` `seg_eq C A C B`] .
	have "bet B F E" using `bet B F E` .
	have "seg_eq B F B F" using congruencereflexiveE[OF `axioms`] by blast
	have "seg_lt B F B E" using lessthan_b[OF `axioms` `bet B F E` `seg_eq B F B F`] .
	have "seg_eq A D B E" using congruencesymmetric[OF `axioms` `seg_eq B E A D`] .
	obtain G where "bet A G D \<and> seg_eq A G B F" using Prop03[OF `axioms` `seg_lt B F B E` `seg_eq A D B E`] by blast
	have "bet A G D" using `bet A G D \<and> seg_eq A G B F` by blast
	have "seg_eq A G B F" using `bet A G D \<and> seg_eq A G B F` by blast
	have "seg_eq G D F E" using differenceofparts[OF `axioms` `seg_eq A G B F` `seg_eq A D B E` `bet A G D` `bet B F E`] .
	have "seg_eq E F D G" using doublereverse[OF `axioms` `seg_eq G D F E`] by blast
	have "seg_eq F B G A" using doublereverse[OF `axioms` `seg_eq A G B F`] by blast
	have "seg_eq A E B D" using `seg_eq A E B D` .
	have "seg_eq E A D B" using congruenceflip[OF `axioms` `seg_eq A E B D`] by blast
	have "seg_eq B A A B" using equalityreverseE[OF `axioms`] by blast
	have "bet E F B" using `bet E F B` .
	have "bet D G A" using betweennesssymmetryE[OF `axioms` `bet A G D`] .
	have "seg_eq F A G B" using interior5[OF `axioms` `bet E F B` `bet D G A` `seg_eq E F D G` `seg_eq F B G A` `seg_eq E A D B` `seg_eq B A A B`] .
	have "seg_eq A F B G" using congruenceflip[OF `axioms` `seg_eq F A G B`] by blast
	have "seg_eq B D A E" using `seg_eq B D A E` .
	have "seg_eq E D D E" using equalityreverseE[OF `axioms`] by blast
	have "seg_eq F D G E" using interior5[OF `axioms` `bet E F B` `bet D G A` `seg_eq E F D G` `seg_eq F B G A` `seg_eq E D D E` `seg_eq B D A E`] .
	have "bet A F D" using `bet A F D` .
	have "seg_eq A F B G" using `seg_eq A F B G` .
	have "seg_eq F D G E" using `seg_eq F D G E` .
	have "seg_eq A D B E" using `seg_eq A D B E` .
	have "bet B G E" using betweennesspreserved[OF `axioms` `seg_eq A F B G` `seg_eq A D B E` `seg_eq F D G E` `bet A F D`] .
	have "bet E G B" using betweennesssymmetryE[OF `axioms` `bet B G E`] .
	have "\<not> (col A D E)"
	proof (rule ccontr)
		assume "col A D E"
		have "col C A E" using collinear_b `axioms` `bet C A E \<and> seg_eq A E A B` by blast
		have "col A E D" using collinearorder[OF `axioms` `col A D E`] by blast
		have "col A E C" using collinearorder[OF `axioms` `col C A E`] by blast
		have "A \<noteq> E" using betweennotequal[OF `axioms` `bet C A E`] by blast
		have "col E D C" using collinear4[OF `axioms` `col A E D` `col A E C` `A \<noteq> E`] .
		have "col E C D" using collinearorder[OF `axioms` `col E D C`] by blast
		have "col E C A" using collinearorder[OF `axioms` `col A E C`] by blast
		have "C \<noteq> E" using betweennotequal[OF `axioms` `bet C A E`] by blast
		have "E \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> E`] .
		have "col C D A" using collinear4[OF `axioms` `col E C D` `col E C A` `E \<noteq> C`] .
		have "col C B D" using collinear_b `axioms` `bet C B D \<and> seg_eq B D A B` by blast
		have "col D C A" using collinearorder[OF `axioms` `col C D A`] by blast
		have "col D C B" using collinearorder[OF `axioms` `col C B D`] by blast
		have "C \<noteq> D" using betweennotequal[OF `axioms` `bet C B D`] by blast
		have "D \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> D`] .
		have "col C A B" using collinear4[OF `axioms` `col D C A` `col D C B` `D \<noteq> C`] .
		have "col A B C" using collinearorder[OF `axioms` `col C A B`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col A D E" by blast
	have "\<not> (col A D B)"
	proof (rule ccontr)
		assume "col A D B"
		have "col D B A" using collinearorder[OF `axioms` `col A D B`] by blast
		have "col C B D" using collinear_b `axioms` `bet C B D \<and> seg_eq B D A B` by blast
		have "col D B C" using collinearorder[OF `axioms` `col C B D`] by blast
		have "B \<noteq> D" using betweennotequal[OF `axioms` `bet C B D`] by blast
		have "D \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> D`] .
		have "col B A C" using collinear4[OF `axioms` `col D B A` `col D B C` `D \<noteq> B`] .
		have "col A B C" using collinearorder[OF `axioms` `col B A C`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col A D B" by blast
	have "cuts A D E B G" using cut_b[OF `axioms` `bet A G D` `bet E G B` `\<not> col A D E` `\<not> col A D B`] .
	have "bet A F D" using `bet A F D` .
	have "bet E F B" using `bet E F B` .
	have "cuts A D E B F" using cut_b[OF `axioms` `bet A F D` `bet E F B` `\<not> col A D E` `\<not> col A D B`] .
	have "\<not> (col D E B)"
	proof (rule ccontr)
		assume "col D E B"
		have "col C B D" using collinear_b `axioms` `bet C B D \<and> seg_eq B D A B` by blast
		have "col D B C" using collinearorder[OF `axioms` `col C B D`] by blast
		have "col D B E" using collinearorder[OF `axioms` `col D E B`] by blast
		have "B \<noteq> D" using betweennotequal[OF `axioms` `bet C B D`] by blast
		have "D \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> D`] .
		have "col B C E" using collinear4[OF `axioms` `col D B C` `col D B E` `D \<noteq> B`] .
		have "col C A E" using collinear_b `axioms` `bet C A E \<and> seg_eq A E A B` by blast
		have "col E C A" using collinearorder[OF `axioms` `col C A E`] by blast
		have "col E C B" using collinearorder[OF `axioms` `col B C E`] by blast
		have "C \<noteq> E" using betweennotequal[OF `axioms` `bet C A E`] by blast
		have "E \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> E`] .
		have "col C A B" using collinear4[OF `axioms` `col E C A` `col E C B` `E \<noteq> C`] .
		have "col A B C" using collinearorder[OF `axioms` `col C A B`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col D E B" by blast
	have "G = F" using twolines[OF `axioms` `cuts A D E B G` `cuts A D E B F` `\<not> col D E B`] .
	have "seg_eq A G B F" using `seg_eq A G B F` .
	have "seg_eq A F B F" using `seg_eq A F B G` `G = F` by blast
	have "seg_eq F A F B" using congruenceflip[OF `axioms` `seg_eq A F B F`] by blast
	have "seg_eq C M C M" using congruencereflexiveE[OF `axioms`] by blast
	have "seg_eq M F M F" using congruencereflexiveE[OF `axioms`] by blast
	have "seg_eq C A C B" using `seg_eq C A C B` .
	have "seg_eq M A M B" using interior5[OF `axioms` `bet C M F` `bet C M F` `seg_eq C M C M` `seg_eq M F M F` `seg_eq C A C B` `seg_eq F A F B`] .
	have "bet A M B \<and> seg_eq M A M B" using `bet A M B \<and> bet C M F` `seg_eq M A M B` by blast
	thus ?thesis by blast
qed

end