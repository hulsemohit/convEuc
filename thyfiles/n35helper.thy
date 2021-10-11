theory n35helper
	imports Geometry NCdistinct NChelper NCorder Prop34 betweennotequal collinear4 collinearbetween collinearorder congruenceflip congruencesymmetric congruencetransitive diagonalsmeet equalitysymmetric inequalitysymmetric lessthancongruence lessthancongruence2 lessthantransitive parallelNC parallelflip trichotomy2
begin

theorem(in euclidean_geometry) n35helper:
	assumes 
		"parallelogram A B C D"
		"parallelogram E B C F"
		"bet A D F"
		"col A E F"
	shows "bet A E F"
proof -
	have "parallel A B C D \<and> parallel A D B C" using parallelogram_f[OF `parallelogram A B C D`] .
	have "parallel E B C F \<and> parallel E F B C" using parallelogram_f[OF `parallelogram E B C F`] .
	have "parallel A B C D" using `parallel A B C D \<and> parallel A D B C` by blast
	have "parallel A D B C" using `parallel A B C D \<and> parallel A D B C` by blast
	have "parallel E B C F" using `parallel E B C F \<and> parallel E F B C` by blast
	have "parallel E F B C" using `parallel E B C F \<and> parallel E F B C` by blast
	have "parallel A B D C" using parallelflip[OF `parallel A B C D`] by blast
	have "parallel E B F C" using parallelflip[OF `parallel E B C F`] by blast
	have "seg_eq A D B C" using Prop34[OF `parallelogram A B C D`] by blast
	have "seg_eq E F B C" using Prop34[OF `parallelogram E B C F`] by blast
	have "seg_eq B C E F" using congruencesymmetric[OF `seg_eq E F B C`] .
	have "seg_eq A D E F" using congruencetransitive[OF `seg_eq A D B C` `seg_eq B C E F`] .
	have "col A D F" using collinear_b `bet A D F` by blast
	have "col F A E" using collinearorder[OF `col A E F`] by blast
	have "col F A D" using collinearorder[OF `col A D F`] by blast
	have "A \<noteq> F" using betweennotequal[OF `bet A D F`] by blast
	have "F \<noteq> A" using inequalitysymmetric[OF `A \<noteq> F`] .
	have "col A E D" using collinear4[OF `col F A E` `col F A D` `F \<noteq> A`] .
	obtain M where "bet A M C \<and> bet B M D" using diagonalsmeet[OF `parallelogram A B C D`]  by  blast
	have "bet A M C" using `bet A M C \<and> bet B M D` by blast
	have "bet B M D" using `bet A M C \<and> bet B M D` by blast
	have "bet D M B" using betweennesssymmetryE[OF `bet B M D`] .
	have "bet B M D" using betweennesssymmetryE[OF `bet D M B`] .
	obtain m where "bet E m C \<and> bet B m F" using diagonalsmeet[OF `parallelogram E B C F`]  by  blast
	have "\<not> col A D B" using parallelNC[OF `parallel A D B C`] by blast
	have "col A D F" using collinear_b `bet A D F` by blast
	have "A = A" using equalityreflexiveE.
	have "col A D A" using collinear_b `A = A` by blast
	have "\<not> col A F B" using NChelper[OF `\<not> col A D B` `col A D A` `col A D F` `A \<noteq> F`] .
	obtain Q where "bet B Q F \<and> bet A M Q" using Pasch_outerE[OF `bet B M D` `bet A D F` `\<not> col A F B`]  by  blast
	have "bet B Q F" using `bet B Q F \<and> bet A M Q` by blast
	have "bet A M Q" using `bet B Q F \<and> bet A M Q` by blast
	have "col A M Q" using collinear_b `bet B Q F \<and> bet A M Q` by blast
	have "col A M C" using collinear_b `bet A M C \<and> bet B M D` by blast
	have "col M A Q" using collinearorder[OF `col A M Q`] by blast
	have "col M A C" using collinearorder[OF `col A M C`] by blast
	have "A \<noteq> M" using betweennotequal[OF `bet A M C`] by blast
	have "M \<noteq> A" using inequalitysymmetric[OF `A \<noteq> M`] .
	have "col A Q C" using collinear4[OF `col M A Q` `col M A C` `M \<noteq> A`] .
	have "A = A" using equalityreflexiveE.
	have "C = C" using equalityreflexiveE.
	have "col F A A" using collinear_b `A = A` by blast
	have "col C C B" using collinear_b `C = C` by blast
	have "A \<noteq> F" using betweennotequal[OF `bet A D F`] by blast
	have "F \<noteq> A" using inequalitysymmetric[OF `A \<noteq> F`] .
	have "B \<noteq> C" using parallel_f[OF `parallel A D B C`] by fastforce
	have "C \<noteq> B" using inequalitysymmetric[OF `B \<noteq> C`] .
	have "\<not> (meets F A C B)"
	proof (rule ccontr)
		assume "\<not> (\<not> (meets F A C B))"
hence "meets F A C B" by blast
		obtain p where "F \<noteq> A \<and> C \<noteq> B \<and> col F A p \<and> col C B p" using meet_f[OF `meets F A C B`]  by  blast
		have "F \<noteq> A" using `F \<noteq> A` .
		have "col F A p" using `F \<noteq> A \<and> C \<noteq> B \<and> col F A p \<and> col C B p` by blast
		have "col C B p" using `F \<noteq> A \<and> C \<noteq> B \<and> col F A p \<and> col C B p` by blast
		have "col A D F" using collinear_b `bet A D F` by blast
		have "col F A D" using collinearorder[OF `col A D F`] by blast
		have "A \<noteq> D" using betweennotequal[OF `bet A D F`] by blast
		have "col A D p" using collinear4[OF `col F A D` `col F A p` `F \<noteq> A`] .
		have "col B C p" using collinearorder[OF `col C B p`] by blast
		have "A \<noteq> D \<and> B \<noteq> C \<and> col A D p \<and> col B C p" using `A \<noteq> D` `B \<noteq> C` `col A D p` `col B C p` by blast
		have "meets A D B C" using meet_b[OF `A \<noteq> D` `B \<noteq> C` `col A D p` `col B C p`] .
		have "\<not> (meets A D B C)" using parallel_f[OF `parallel A D B C`] by fastforce
		show "False" using `\<not> (meets A D B C)` `meets A D B C` by blast
	qed
	hence "\<not> (meets F A C B)" by blast
	have "bet F Q B" using betweennesssymmetryE[OF `bet B Q F`] .
	have "col A C Q" using collinearorder[OF `col A Q C`] by blast
	have "bet A Q C" using collinearbetween[OF `col F A A` `col C C B` `F \<noteq> A` `C \<noteq> B` `F \<noteq> A` `C \<noteq> B` `\<not> (meets F A C B)` `bet F Q B` `col A C Q`] .
	have "bet C Q A" using betweennesssymmetryE[OF `bet A Q C`] .
	have "\<not> (A = E)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> E)"
		hence "A = E" by blast
		have "seg_eq A F A F" using congruencereflexiveE.
		have "seg_eq A F E F" using `seg_eq A F A F` `A = E` by blast
		have "seg_eq A D E F" using `seg_eq A D E F` .
		have "seg_eq E F A D" using congruencesymmetric[OF `seg_eq A D E F`] .
		have "seg_eq A F A D" using congruencetransitive[OF `seg_eq A F E F` `seg_eq E F A D`] .
		have "seg_eq A D A F" using congruencesymmetric[OF `seg_eq A F A D`] .
		have "bet A D F" using `bet A D F` .
		have "seg_eq A D A D" using congruencereflexiveE.
		have "seg_lt A D A F" using lessthan_b[OF `bet A D F` `seg_eq A D A D`] .
		have "seg_lt A F A F" using lessthancongruence2[OF `seg_lt A D A F` `seg_eq A D A F`] .
		have "\<not> (seg_lt A F A F)" using trichotomy2[OF `seg_lt A F A F`] .
		show "False" using `\<not> (seg_lt A F A F)` `seg_lt A F A F` by blast
	qed
	hence "A \<noteq> E" by blast
	have "\<not> (bet A F E)"
	proof (rule ccontr)
		assume "\<not> (\<not> (bet A F E))"
hence "bet A F E" by blast
		have "bet E F A" using betweennesssymmetryE[OF `bet A F E`] .
		have "\<not> col A D C" using parallelNC[OF `parallel A B D C`] by blast
		have "col A D E" using collinearorder[OF `col A E D`] by blast
		have "A \<noteq> E" using `A \<noteq> E` .
		have "\<not> col A E C" using NChelper[OF `\<not> col A D C` `col A D A` `col A D E` `A \<noteq> E`] .
		have "\<not> col C A E" using NCorder[OF `\<not> col A E C`] by blast
		obtain r where "bet C r F \<and> bet E r Q" using Pasch_innerE[OF `bet C Q A` `bet E F A` `\<not> col C A E`]  by  blast
		have "bet C r F" using `bet C r F \<and> bet E r Q` by blast
		have "bet E r Q" using `bet C r F \<and> bet E r Q` by blast
		have "bet F Q B" using `bet F Q B` .
		have "\<not> col E B F" using parallelNC[OF `parallel E B C F`] by blast
		have "\<not> col F B E" using NCorder[OF `\<not> col E B F`] by blast
		obtain H where "bet E H B \<and> bet F r H" using Pasch_outerE[OF `bet E r Q` `bet F Q B` `\<not> col F B E`]  by  blast
		have "bet E H B" using `bet E H B \<and> bet F r H` by blast
		have "bet F r H" using `bet E H B \<and> bet F r H` by blast
		have "col E H B" using collinear_b `bet E H B \<and> bet F r H` by blast
		have "col F r H" using collinear_b `bet E H B \<and> bet F r H` by blast
		have "col E B H" using collinearorder[OF `col E H B`] by blast
		have "col C r F" using collinear_b `bet C r F \<and> bet E r Q` by blast
		have "col r F C" using collinearorder[OF `col C r F`] by blast
		have "col r F H" using collinearorder[OF `col F r H`] by blast
		have "r \<noteq> F" using betweennotequal[OF `bet C r F`] by blast
		have "col F C H" using collinear4[OF `col r F C` `col r F H` `r \<noteq> F`] .
		have "parallel E B F C" using `parallel E B F C` .
		have "B \<noteq> E" using NCdistinct[OF `\<not> col E B F`] by blast
		have "E \<noteq> B" using inequalitysymmetric[OF `B \<noteq> E`] .
		have "F \<noteq> C" using parallel_f[OF `parallel E B F C`] by fastforce
		have "E \<noteq> B \<and> F \<noteq> C \<and> col E B H \<and> col F C H" using `E \<noteq> B` `F \<noteq> C` `col E B H` `col F C H` by blast
		have "meets E B F C" using meet_b[OF `E \<noteq> B` `F \<noteq> C` `col E B H` `col F C H`] .
		have "\<not> (meets E B F C)" using parallel_f[OF `parallel E B F C`] by fastforce
		show "False" using `\<not> (meets E B F C)` `meets E B F C` by blast
	qed
	hence "\<not> (bet A F E)" by blast
	have "col A F E" using collinearorder[OF `col A E F`] by blast
	have "A = F \<or> A = E \<or> F = E \<or> bet F A E \<or> bet A F E \<or> bet A E F" using collinear_f[OF `col A F E`] .
	consider "A = F"|"A = E"|"F = E"|"bet F A E"|"bet A F E"|"bet A E F" using `A = F \<or> A = E \<or> F = E \<or> bet F A E \<or> bet A F E \<or> bet A E F`  by blast
	hence "bet A E F"
	proof (cases)
		assume "A = F"
		have "\<not> (\<not> (bet A E F))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet A E F)))"
hence "\<not> (bet A E F)" by blast
			have "bet A D F" using `bet A D F` .
			have "bet A D A" using `bet A D F` `A = F` by blast
			have "\<not> (bet A D A)" using betweennessidentityE.
			show "False" using `\<not> (bet A D A)` `bet A D A` by blast
		qed
		hence "bet A E F" by blast
		thus ?thesis by blast
	next
		assume "A = E"
		have "\<not> (\<not> (bet A E F))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet A E F)))"
hence "\<not> (bet A E F)" by blast
			have "A \<noteq> E" using `A \<noteq> E` .
			show "False" using `A \<noteq> E` `A = E` by blast
		qed
		hence "bet A E F" by blast
		thus ?thesis by blast
	next
		assume "F = E"
		have "\<not> (\<not> (bet A E F))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet A E F)))"
hence "\<not> (bet A E F)" by blast
			have "E = F" using equalitysymmetric[OF `F = E`] .
			have "col B E F" using collinear_b `E = F` by blast
			have "col E B F" using collinearorder[OF `col B E F`] by blast
			have "F = F" using equalityreflexiveE.
			have "col F C F" using collinear_b `F = F` by blast
			have "E \<noteq> B" using parallel_f[OF `parallel E B C F`] by fastforce
			have "F \<noteq> C" using parallel_f[OF `parallel E B F C`] by fastforce
			have "E \<noteq> B \<and> F \<noteq> C \<and> col E B F \<and> col F C F" using `E \<noteq> B` `F \<noteq> C` `col E B F` `col F C F` by blast
			have "meets E B F C" using meet_b[OF `E \<noteq> B` `F \<noteq> C` `col E B F` `col F C F`] .
			have "\<not> (meets E B F C)" using parallel_f[OF `parallel E B F C`] by fastforce
			show "False" using `\<not> (meets E B F C)` `meets E B F C` by blast
		qed
		hence "bet A E F" by blast
		thus ?thesis by blast
	next
		assume "bet F A E"
		have "\<not> (\<not> (bet A E F))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet A E F)))"
hence "\<not> (bet A E F)" by blast
			have "seg_eq A D A D" using congruencereflexiveE.
			have "seg_lt A D A F" using lessthan_b[OF `bet A D F` `seg_eq A D A D`] .
			have "seg_eq A D D A" using equalityreverseE.
			have "seg_lt D A A F" using lessthancongruence2[OF `seg_lt A D A F` `seg_eq A D D A`] .
			have "seg_eq A F F A" using equalityreverseE.
			have "seg_lt D A F A" using lessthancongruence[OF `seg_lt D A A F` `seg_eq A F F A`] .
			have "seg_eq F A F A" using congruencereflexiveE.
			have "seg_lt F A F E" using lessthan_b[OF `bet F A E` `seg_eq F A F A`] .
			have "seg_lt D A F E" using lessthantransitive[OF `seg_lt D A F A` `seg_lt F A F E`] .
			have "seg_eq D A F E" using congruenceflip[OF `seg_eq A D E F`] by blast
			have "seg_lt F E F E" using lessthancongruence2[OF `seg_lt D A F E` `seg_eq D A F E`] .
			have "\<not> (seg_lt F E F E)" using trichotomy2[OF `seg_lt F E F E`] .
			show "False" using `\<not> (seg_lt F E F E)` `seg_lt F E F E` by blast
		qed
		hence "bet A E F" by blast
		thus ?thesis by blast
	next
		assume "bet A F E"
		have "\<not> (\<not> (bet A E F))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet A E F)))"
hence "\<not> (bet A E F)" by blast
			have "\<not> (bet A F E)" using `\<not> (bet A F E)` .
			show "False" using `\<not> (bet A F E)` `bet A F E` by blast
		qed
		hence "bet A E F" by blast
		thus ?thesis by blast
	next
		assume "bet A E F"
		have "bet A E F" using `bet A E F` .
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end