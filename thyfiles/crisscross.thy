theory crisscross
	imports n3_5b n3_6b Geometry NCdistinct NChelper NCorder betweennotequal collinear4 collinearbetween collinearorder collinearparallel inequalitysymmetric parallelNC paralleldef2B parallelflip parallelsymmetric planeseparation samesidesymmetric
begin

theorem(in euclidean_geometry) crisscross:
	assumes 
		"parallel A C B D"
		"\<not> (cross A B C D)"
	shows "cross A D B C"
proof -
	have "parallel B D A C" using parallelsymmetric[OF `parallel A C B D`] .
	have "tarski_parallel B D A C" using paralleldef2B[OF `parallel B D A C`] .
	have "same_side A C B D" using tarski_parallel_f[OF `tarski_parallel B D A C`] by blast
	have "\<not> col A C B" using parallelNC[OF `parallel A C B D`] by blast
	have "A \<noteq> B" using NCdistinct[OF `\<not> col A C B`] by blast
	obtain E where "bet A B E \<and> seg_eq B E A B" using extensionE[OF `A \<noteq> B` `A \<noteq> B`]  by  blast
	have "bet A B E" using `bet A B E \<and> seg_eq B E A B` by blast
	have "B = B" using equalityreflexiveE.
	have "col B D B" using collinear_b `B = B` by blast
	have "\<not> col A B D" using parallelNC[OF `parallel A C B D`] by blast
	have "\<not> col B D A" using NCorder[OF `\<not> col A B D`] by blast
	have "same_side C A B D" using samesidesymmetric[OF `same_side A C B D`] by blast
	have "oppo_side A B D E" using oppositeside_b[OF `bet A B E` `col B D B` `\<not> col B D A`] .
	have "oppo_side C B D E" using planeseparation[OF `same_side C A B D` `oppo_side A B D E`] .
	obtain F where "bet C F E \<and> col B D F \<and> \<not> col B D C" using oppositeside_f[OF `oppo_side C B D E`]  by  blast
	have "bet C F E" using `bet C F E \<and> col B D F \<and> \<not> col B D C` by blast
	have "col B D F" using `bet C F E \<and> col B D F \<and> \<not> col B D C` by blast
	have "\<not> col B D C" using `bet C F E \<and> col B D F \<and> \<not> col B D C` by blast
	have "B \<noteq> D" using NCdistinct[OF `\<not> col A B D`] by blast
	have "\<not> col A B D" using parallelNC[OF `parallel A C B D`] by blast
	have "A \<noteq> D" using NCdistinct[OF `\<not> col A B D`] by blast
	have "\<not> col A C D" using parallelNC[OF `parallel A C B D`] by blast
	have "A \<noteq> C" using NCdistinct[OF `\<not> col A C B`] by blast
	have "C \<noteq> D" using NCdistinct[OF `\<not> col A C D`] by blast
	have "C \<noteq> A" using inequalitysymmetric[OF `A \<noteq> C`] .
	have "\<not> col A C B" using parallelNC[OF `parallel A C B D`] by blast
	have "C \<noteq> B" using NCdistinct[OF `\<not> col A C B`] by blast
	have "B \<noteq> C" using inequalitysymmetric[OF `C \<noteq> B`] .
	have "B = D \<or> B = F \<or> D = F \<or> bet D B F \<or> bet B D F \<or> bet B F D" using collinear_f[OF `col B D F`] .
	consider "B = D"|"B = F"|"D = F"|"bet D B F"|"bet B D F"|"bet B F D" using `B = D \<or> B = F \<or> D = F \<or> bet D B F \<or> bet B D F \<or> bet B F D`  by blast
	hence "cross A D B C"
	proof (cases)
		assume "B = D"
		have "\<not> (\<not> (cross A D B C))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (cross A D B C)))"
hence "\<not> (cross A D B C)" by blast
			have "B \<noteq> D" using `B \<noteq> D` .
			show "False" using `B \<noteq> D` `B = D` by blast
		qed
		hence "cross A D B C" by blast
		thus ?thesis by blast
	next
		assume "B = F"
		have "\<not> (\<not> (cross A D B C))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (cross A D B C)))"
hence "\<not> (cross A D B C)" by blast
			have "col C F E" using collinear_b `bet C F E \<and> col B D F \<and> \<not> col B D C` by blast
			have "col E F C" using collinearorder[OF `col C F E`] by blast
			have "B \<noteq> E" using betweennotequal[OF `bet A B E`] by blast
			have "col A B E" using collinear_b `bet A B E \<and> seg_eq B E A B` by blast
			have "col E B A" using collinearorder[OF `col A B E`] by blast
			have "col E F C" using collinearorder[OF `col C F E`] by blast
			have "col E B C" using `col E F C` `B = F` by blast
			have "E \<noteq> B" using inequalitysymmetric[OF `B \<noteq> E`] .
			have "col B A C" using collinear4[OF `col E B A` `col E B C` `E \<noteq> B`] .
			have "col A C B" using collinearorder[OF `col B A C`] by blast
			have "\<not> col A C B" using parallelNC[OF `parallel A C B D`] by blast
			show "False" using `\<not> col A C B` `col A C B` by blast
		qed
		hence "cross A D B C" by blast
		thus ?thesis by blast
	next
		assume "D = F"
		have "\<not> col A C B" using parallelNC[OF `parallel A C B D`] by blast
		have "\<not> col A C F" using `\<not> col A C D` `D = F` by blast
		have "\<not> col C F A" using NCorder[OF `\<not> col A C F`] by blast
		have "col C F E" using collinear_b `bet C F E \<and> col B D F \<and> \<not> col B D C` by blast
		have "C = C" using equalityreflexiveE.
		have "col C F C" using collinear_b `C = C` by blast
		have "C \<noteq> E" using betweennotequal[OF `bet C F E`] by blast
		have "\<not> col C E A" using NChelper[OF `\<not> col C F A` `col C F C` `col C F E` `C \<noteq> E`] .
		have "\<not> col A E C" using NCorder[OF `\<not> col C E A`] by blast
		obtain M where "bet A M F \<and> bet C M B" using Pasch_innerE[OF `bet A B E` `bet C F E` `\<not> col A E C`]  by  blast
		have "bet A M F" using `bet A M F \<and> bet C M B` by blast
		have "bet C M B" using `bet A M F \<and> bet C M B` by blast
		have "bet A M D" using `bet A M F` `D = F` by blast
		have "bet B M C" using betweennesssymmetryE[OF `bet C M B`] .
		have "A \<noteq> D \<and> B \<noteq> C \<and> bet A M D \<and> bet B M C" using `A \<noteq> D` `B \<noteq> C` `bet A M D` `bet B M C` by blast
		have "cross A D B C" using cross_b[OF `bet A M D` `bet B M C`] .
		thus ?thesis by blast
	next
		assume "bet D B F"
		have "\<not> (\<not> (cross A D B C))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (cross A D B C)))"
hence "\<not> (cross A D B C)" by blast
			have "bet C F E" using `bet C F E` .
			have "\<not> col D B C" using NCorder[OF `\<not> col B D C`] by blast
			have "D = D" using equalityreflexiveE.
			have "col D B D" using collinear_b `D = D` by blast
			have "col D B F" using collinearorder[OF `col B D F`] by blast
			have "D \<noteq> F" using betweennotequal[OF `bet D B F`] by blast
			have "\<not> col D F C" using NChelper[OF `\<not> col D B C` `col D B D` `col D B F` `D \<noteq> F`] .
			have "\<not> col C F D" using NCorder[OF `\<not> col D F C`] by blast
			have "col C F E" using collinear_b `bet C F E \<and> col B D F \<and> \<not> col B D C` by blast
			have "C = C" using equalityreflexiveE.
			have "col C F C" using collinear_b `C = C` by blast
			have "C \<noteq> E" using betweennotequal[OF `bet C F E`] by blast
			have "\<not> col C E D" using NChelper[OF `\<not> col C F D` `col C F C` `col C F E` `C \<noteq> E`] .
			have "\<not> col E C D" using NCorder[OF `\<not> col C E D`] by blast
			have "bet E F C" using betweennesssymmetryE[OF `bet C F E`] .
			obtain M where "bet D M C \<and> bet E B M" using Pasch_outerE[OF `bet D B F` `bet E F C` `\<not> col E C D`]  by  blast
			have "bet D M C" using `bet D M C \<and> bet E B M` by blast
			have "bet E B M" using `bet D M C \<and> bet E B M` by blast
			have "bet C M D" using betweennesssymmetryE[OF `bet D M C`] .
			have "bet M B E" using betweennesssymmetryE[OF `bet E B M`] .
			have "col A B E" using collinear_b `bet A B E \<and> seg_eq B E A B` by blast
			have "col E B M" using collinear_b `bet D M C \<and> bet E B M` by blast
			have "col E B A" using collinearorder[OF `col A B E`] by blast
			have "B \<noteq> E" using betweennotequal[OF `bet A B E`] by blast
			have "E \<noteq> B" using inequalitysymmetric[OF `B \<noteq> E`] .
			have "col B M A" using collinear4[OF `col E B M` `col E B A` `E \<noteq> B`] .
			have "col A B M" using collinearorder[OF `col B M A`] by blast
			have "parallel C A B D" using parallelflip[OF `parallel A C B D`] by blast
			have "\<not> (meets C A B D)" using parallel_f[OF `parallel C A B D`] by fastforce
			have "A = A" using equalityreflexiveE.
			have "col C A A" using collinear_b `A = A` by blast
			have "B = B" using equalityreflexiveE.
			have "col B B D" using collinear_b `B = B` by blast
			have "C \<noteq> A" using `C \<noteq> A` .
			have "B \<noteq> D" using `B \<noteq> D` .
			have "col A B M" using `col A B M` .
			have "bet A M B" using collinearbetween[OF `col C A A` `col B B D` `C \<noteq> A` `B \<noteq> D` `C \<noteq> A` `B \<noteq> D` `\<not> (meets C A B D)` `bet C M D` `col A B M`] .
			have "A \<noteq> B \<and> C \<noteq> D \<and> bet A M B \<and> bet C M D" using `A \<noteq> B` `C \<noteq> D` `bet A M B` `bet C M D` by blast
			have "cross A B C D" using cross_b[OF `bet A M B` `bet C M D`] .
			have "\<not> (cross A B C D)" using `\<not> (cross A B C D)` .
			show "False" using `\<not> (cross A B C D)` `cross A B C D` by blast
		qed
		hence "cross A D B C" by blast
		thus ?thesis by blast
	next
		assume "bet B D F"
		have "bet C F E" using `bet C F E` .
		have "\<not> col A C B" using parallelNC[OF `parallel A C B D`] by blast
		have "A = A" using equalityreflexiveE.
		have "col A B A" using collinear_b `A = A` by blast
		have "col A B E" using collinear_b `bet A B E \<and> seg_eq B E A B` by blast
		have "A \<noteq> E" using betweennotequal[OF `bet A B E`] by blast
		have "\<not> col A B C" using NCorder[OF `\<not> col A C B`] by blast
		have "\<not> col A E C" using NChelper[OF `\<not> col A B C` `col A B A` `col A B E` `A \<noteq> E`] .
		have "col A E B" using collinearorder[OF `col A B E`] by blast
		have "E = E" using equalityreflexiveE.
		have "col A E E" using collinear_b `E = E` by blast
		have "B \<noteq> E" using betweennotequal[OF `bet A B E`] by blast
		have "\<not> col B E C" using NChelper[OF `\<not> col A E C` `col A E B` `col A E E` `B \<noteq> E`] .
		have "\<not> col C E B" using NCorder[OF `\<not> col B E C`] by blast
		obtain J where "bet B J E \<and> bet C D J" using Pasch_outerE[OF `bet B D F` `bet C F E` `\<not> col C E B`]  by  blast
		have "bet B J E" using `bet B J E \<and> bet C D J` by blast
		have "bet A B E" using `bet A B E` .
		have "bet A J E" using n3_5b[OF `bet A B E` `bet B J E`] .
		have "\<not> col A C B" using parallelNC[OF `parallel A C B D`] by blast
		have "\<not> col A B C" using NCorder[OF `\<not> col A C B`] by blast
		have "col A J E" using collinear_b `bet A J E` by blast
		have "col E A B" using collinearorder[OF `col A B E`] by blast
		have "col E A J" using collinearorder[OF `col A J E`] by blast
		have "A \<noteq> E" using betweennotequal[OF `bet A B E`] by blast
		have "E \<noteq> A" using inequalitysymmetric[OF `A \<noteq> E`] .
		have "col A B J" using collinear4[OF `col E A B` `col E A J` `E \<noteq> A`] .
		have "A \<noteq> J" using betweennotequal[OF `bet A J E`] by blast
		have "\<not> col A J C" using NChelper[OF `\<not> col A B C` `col A B A` `col A B J` `A \<noteq> J`] .
		have "bet B J E" using `bet B J E` .
		have "bet A B E" using `bet A B E` .
		have "bet A B J" using innertransitivityE[OF `bet A B E` `bet B J E`] .
		have "bet C D J" using `bet B J E \<and> bet C D J` by blast
		obtain M where "bet A M D \<and> bet C M B" using Pasch_innerE[OF `bet A B J` `bet C D J` `\<not> col A J C`]  by  blast
		have "bet A M D" using `bet A M D \<and> bet C M B` by blast
		have "bet C M B" using `bet A M D \<and> bet C M B` by blast
		have "bet B M C" using betweennesssymmetryE[OF `bet C M B`] .
		have "bet A M D \<and> bet B M C" using `bet A M D \<and> bet C M B` `bet B M C` by blast
		have "cross A D B C" using cross_b[OF `bet A M D` `bet B M C`] .
		thus ?thesis by blast
	next
		assume "bet B F D"
		have "bet D F B" using betweennesssymmetryE[OF `bet B F D`] .
		have "bet E B A" using betweennesssymmetryE[OF `bet A B E`] .
		have "\<not> col A B D" using parallelNC[OF `parallel A C B D`] by blast
		have "col A B E" using collinear_b `bet A B E \<and> seg_eq B E A B` by blast
		have "A = A" using equalityreflexiveE.
		have "col A B A" using collinear_b `A = A` by blast
		have "A \<noteq> E" using betweennotequal[OF `bet A B E`] by blast
		have "\<not> col A E D" using NChelper[OF `\<not> col A B D` `col A B A` `col A B E` `A \<noteq> E`] .
		have "\<not> col E A D" using NCorder[OF `\<not> col A E D`] by blast
		obtain Q where "bet D Q A \<and> bet E F Q" using Pasch_outerE[OF `bet D F B` `bet E B A` `\<not> col E A D`]  by  blast
		have "bet D Q A" using `bet D Q A \<and> bet E F Q` by blast
		have "bet E F Q" using `bet D Q A \<and> bet E F Q` by blast
		have "bet E F C" using betweennesssymmetryE[OF `bet C F E`] .
		have "col E F Q" using collinear_b `bet D Q A \<and> bet E F Q` by blast
		have "col E F C" using collinear_b `bet E F C` by blast
		have "F \<noteq> E" using betweennotequal[OF `bet C F E`] by blast
		have "E \<noteq> F" using inequalitysymmetric[OF `F \<noteq> E`] .
		have "col F Q C" using collinear4[OF `col E F Q` `col E F C` `E \<noteq> F`] .
		have "col F C Q" using collinearorder[OF `col F Q C`] by blast
		have "bet A Q D" using betweennesssymmetryE[OF `bet D Q A`] .
		have "parallel A C B D" using `parallel A C B D` .
		have "col B F D" using collinear_b `bet B F D` by blast
		have "col B D F" using collinearorder[OF `col B F D`] by blast
		have "F \<noteq> D" using betweennotequal[OF `bet B F D`] by blast
		have "parallel A C F D" using collinearparallel[OF `parallel A C B D` `col B D F` `F \<noteq> D`] .
		have "\<not> (meets A C F D)" using parallel_f[OF `parallel A C F D`] by fastforce
		have "C = C" using equalityreflexiveE.
		have "F = F" using equalityreflexiveE.
		have "col A C C" using collinear_b `C = C` by blast
		have "col F F D" using collinear_b `F = F` by blast
		have "A \<noteq> C" using `A \<noteq> C` .
		have "F \<noteq> D" using `F \<noteq> D` .
		have "col C F Q" using collinearorder[OF `col F C Q`] by blast
		have "bet C Q F" using collinearbetween[OF `col A C C` `col F F D` `A \<noteq> C` `F \<noteq> D` `A \<noteq> C` `F \<noteq> D` `\<not> (meets A C F D)` `bet A Q D` `col C F Q`] .
		have "\<not> col A C B" using parallelNC[OF `parallel A C B D`] by blast
		have "\<not> col A B C" using NCorder[OF `\<not> col A C B`] by blast
		have "col A B A" using collinear_b `A = A` by blast
		have "col A B E" using collinear_b `bet A B E \<and> seg_eq B E A B` by blast
		have "A \<noteq> E" using betweennotequal[OF `bet A B E`] by blast
		have "\<not> col A E C" using NChelper[OF `\<not> col A B C` `col A B A` `col A B E` `A \<noteq> E`] .
		have "bet A B E" using `bet A B E` .
		have "bet C Q E" using n3_6b[OF `bet C Q F` `bet C F E`] .
		obtain M where "bet A M Q \<and> bet C M B" using Pasch_innerE[OF `bet A B E` `bet C Q E` `\<not> col A E C`]  by  blast
		have "bet A M Q" using `bet A M Q \<and> bet C M B` by blast
		have "bet C M B" using `bet A M Q \<and> bet C M B` by blast
		have "bet A M D" using n3_6b[OF `bet A M Q` `bet A Q D`] .
		have "bet B M C" using betweennesssymmetryE[OF `bet C M B`] .
		have "cross A D B C" using cross_b[OF `bet A M D` `bet B M C`] .
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end