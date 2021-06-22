theory crisscross
	imports Axioms Definitions Theorems
begin

theorem crisscross:
	assumes: `axioms`
		"parallel A C B D"
		"\<not> (cross A B C D)"
	shows: "cross A D B C"
proof -
	have "parallel B D A C" using parallelsymmetric[OF `axioms` `parallel A C B D`] .
	have "tarski_parallel B D A C" using paralleldef2B[OF `axioms` `parallel B D A C`] .
	have "same_side A C B D" sorry
	have "\<not> col A C B" using parallelNC[OF `axioms` `parallel A C B D`] by blast
	have "A \<noteq> B" using NCdistinct[OF `axioms` `\<not> col A C B`] by blast
	obtain E where "bet A B E \<and> seg_eq B E A B" using extensionE[OF `axioms` `A \<noteq> B` `A \<noteq> B`]  by  blast
	have "bet A B E" using `bet A B E \<and> seg_eq B E A B` by blast
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "col B D B" using col_b `axioms` `B = B` by blast
	have "\<not> col A B D" using parallelNC[OF `axioms` `parallel A C B D`] by blast
	have "\<not> col B D A" using NCorder[OF `axioms` `\<not> col A B D`] by blast
	have "same_side C A B D" using samesidesymmetric[OF `axioms` `same_side A C B D`] by blast
	have "oppo_side A B D E" sorry
	have "oppo_side C B D E" using planeseparation[OF `axioms` `same_side C A B D` `oppo_side A B D E`] .
	obtain F where "bet C F E \<and> col B D F \<and> \<not> col B D C" sorry
	have "bet C F E" using `bet C F E \<and> col B D F \<and> \<not> col B D C` by blast
	have "col B D F" using `bet C F E \<and> col B D F \<and> \<not> col B D C` by blast
	have "\<not> col B D C" using `bet C F E \<and> col B D F \<and> \<not> col B D C` by blast
	have "B \<noteq> D" using NCdistinct[OF `axioms` `\<not> col A B D`] by blast
	have "\<not> col A B D" using parallelNC[OF `axioms` `parallel A C B D`] by blast
	have "A \<noteq> D" using NCdistinct[OF `axioms` `\<not> col A B D`] by blast
	have "\<not> col A C D" using parallelNC[OF `axioms` `parallel A C B D`] by blast
	have "A \<noteq> C" using NCdistinct[OF `axioms` `\<not> col A C B`] by blast
	have "C \<noteq> D" using NCdistinct[OF `axioms` `\<not> col A C D`] by blast
	have "C \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> C`] .
	have "\<not> col A C B" using parallelNC[OF `axioms` `parallel A C B D`] by blast
	have "C \<noteq> B" using NCdistinct[OF `axioms` `\<not> col A C B`] by blast
	have "B \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> B`] .
	have "B = D \<or> B = F \<or> D = F \<or> bet D B F \<or> bet B D F \<or> bet B F D" using col_f[OF `axioms` `col B D F`] .
	consider "B = D"|"B = F"|"D = F"|"bet D B F"|"bet B D F"|"bet B F D" using `B = D \<or> B = F \<or> D = F \<or> bet D B F \<or> bet B D F \<or> bet B F D`  by blast
	hence cross A D B C
	proof (cases)
		case 1
		have "cross A D B C"
		proof (rule ccontr)
			assume "\<not> (cross A D B C)"
			have "B \<noteq> D" using `B \<noteq> D` .
			show "False" using `B \<noteq> D` `B = D` by blast
		qed
		hence "cross A D B C" by blast
	next
		case 2
		have "cross A D B C"
		proof (rule ccontr)
			assume "\<not> (cross A D B C)"
			have "col C F E" using col_b `axioms` `bet C F E \<and> col B D F \<and> \<not> col B D C` by blast
			have "col E F C" using collinearorder[OF `axioms` `col C F E`] by blast
			have "B \<noteq> E" using betweennotequal[OF `axioms` `bet A B E`] by blast
			have "col A B E" using col_b `axioms` `bet A B E \<and> seg_eq B E A B` by blast
			have "col E B A" using collinearorder[OF `axioms` `col A B E`] by blast
			have "col E F C" using collinearorder[OF `axioms` `col C F E`] by blast
			have "col E B C" sorry
			have "E \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> E`] .
			have "col B A C" using collinear4[OF `axioms` `col E B A` `col E B C` `E \<noteq> B`] .
			have "col A C B" using collinearorder[OF `axioms` `col B A C`] by blast
			have "\<not> col A C B" using parallelNC[OF `axioms` `parallel A C B D`] by blast
			show "False" using `\<not> col A C B` `col A C B` by blast
		qed
		hence "cross A D B C" by blast
	next
		case 3
		have "\<not> col A C B" using parallelNC[OF `axioms` `parallel A C B D`] by blast
		have "\<not> col A C F" sorry
		have "\<not> col C F A" using NCorder[OF `axioms` `\<not> col A C F`] by blast
		have "col C F E" using col_b `axioms` `bet C F E \<and> col B D F \<and> \<not> col B D C` by blast
		have "C = C" using equalityreflexiveE[OF `axioms`] .
		have "col C F C" using col_b `axioms` `C = C` by blast
		have "C \<noteq> E" using betweennotequal[OF `axioms` `bet C F E`] by blast
		have "\<not> col C E A" using NChelper[OF `axioms` `\<not> col C F A` `col C F C` `col C F E` `C \<noteq> E`] .
		have "\<not> col A E C" using NCorder[OF `axioms` `\<not> col C E A`] by blast
		obtain M where "bet A M F \<and> bet C M B" using Pasch-innerE[OF `axioms` `bet A B E` `bet C F E` `\<not> col A E C`]  by  blast
		have "bet A M F" using `bet A M F \<and> bet C M B` by blast
		have "bet C M B" using `bet A M F \<and> bet C M B` by blast
		have "bet A M D" sorry
		have "bet B M C" using betweennesssymmetryE[OF `axioms` `bet C M B`] .
		have "A \<noteq> D \<and> B \<noteq> C \<and> bet A M D \<and> bet B M C" using `A \<noteq> D` `B \<noteq> C` `bet A M D` `bet B M C` by blast
		have "cross A D B C" sorry
	next
		case 4
		have "cross A D B C"
		proof (rule ccontr)
			assume "\<not> (cross A D B C)"
			have "bet C F E" using `bet C F E` .
			have "\<not> col D B C" using NCorder[OF `axioms` `\<not> col B D C`] by blast
			have "D = D" using equalityreflexiveE[OF `axioms`] .
			have "col D B D" using col_b `axioms` `D = D` by blast
			have "col D B F" using collinearorder[OF `axioms` `col B D F`] by blast
			have "D \<noteq> F" using betweennotequal[OF `axioms` `bet D B F`] by blast
			have "\<not> col D F C" using NChelper[OF `axioms` `\<not> col D B C` `col D B D` `col D B F` `D \<noteq> F`] .
			have "\<not> col C F D" using NCorder[OF `axioms` `\<not> col D F C`] by blast
			have "col C F E" using col_b `axioms` `bet C F E \<and> col B D F \<and> \<not> col B D C` by blast
			have "C = C" using equalityreflexiveE[OF `axioms`] .
			have "col C F C" using col_b `axioms` `C = C` by blast
			have "C \<noteq> E" using betweennotequal[OF `axioms` `bet C F E`] by blast
			have "\<not> col C E D" using NChelper[OF `axioms` `\<not> col C F D` `col C F C` `col C F E` `C \<noteq> E`] .
			have "\<not> col E C D" using NCorder[OF `axioms` `\<not> col C E D`] by blast
			have "bet E F C" using betweennesssymmetryE[OF `axioms` `bet C F E`] .
			obtain M where "bet D M C \<and> bet E B M" using Pasch-outerE[OF `axioms` `bet D B F` `bet E F C` `\<not> col E C D`]  by  blast
			have "bet D M C" using `bet D M C \<and> bet E B M` by blast
			have "bet E B M" using `bet D M C \<and> bet E B M` by blast
			have "bet C M D" using betweennesssymmetryE[OF `axioms` `bet D M C`] .
			have "bet M B E" using betweennesssymmetryE[OF `axioms` `bet E B M`] .
			have "col A B E" using col_b `axioms` `bet A B E \<and> seg_eq B E A B` by blast
			have "col E B M" using col_b `axioms` `bet D M C \<and> bet E B M` by blast
			have "col E B A" using collinearorder[OF `axioms` `col A B E`] by blast
			have "B \<noteq> E" using betweennotequal[OF `axioms` `bet A B E`] by blast
			have "E \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> E`] .
			have "col B M A" using collinear4[OF `axioms` `col E B M` `col E B A` `E \<noteq> B`] .
			have "col A B M" using collinearorder[OF `axioms` `col B M A`] by blast
			have "parallel C A B D" using parallelflip[OF `axioms` `parallel A C B D`] by blast
			have "\<not> (meets C A B D)" sorry
			have "A = A" using equalityreflexiveE[OF `axioms`] .
			have "col C A A" using col_b `axioms` `A = A` by blast
			have "B = B" using equalityreflexiveE[OF `axioms`] .
			have "col B B D" using col_b `axioms` `B = B` by blast
			have "C \<noteq> A" using `C \<noteq> A` .
			have "B \<noteq> D" using `B \<noteq> D` .
			have "col A B M" using `col A B M` .
			have "bet A M B" using collinearbetween[OF `axioms` `col C A A` `col B B D` `C \<noteq> A` `B \<noteq> D` `C \<noteq> A` `B \<noteq> D` `\<not> (meets C A B D)` `bet C M D` `col A B M`] .
			have "A \<noteq> B \<and> C \<noteq> D \<and> bet A M B \<and> bet C M D" using `A \<noteq> B` `C \<noteq> D` `bet A M B` `bet C M D` by blast
			have "cross A B C D" sorry
			have "\<not> (cross A B C D)" using `\<not> (cross A B C D)` .
			show "False" using `\<not> (cross A B C D)` `cross A B C D` by blast
		qed
		hence "cross A D B C" by blast
	next
		case 5
		have "bet C F E" using `bet C F E` .
		have "\<not> col A C B" using parallelNC[OF `axioms` `parallel A C B D`] by blast
		have "A = A" using equalityreflexiveE[OF `axioms`] .
		have "col A B A" using col_b `axioms` `A = A` by blast
		have "col A B E" using col_b `axioms` `bet A B E \<and> seg_eq B E A B` by blast
		have "A \<noteq> E" using betweennotequal[OF `axioms` `bet A B E`] by blast
		have "\<not> col A B C" using NCorder[OF `axioms` `\<not> col A C B`] by blast
		have "\<not> col A E C" using NChelper[OF `axioms` `\<not> col A B C` `col A B A` `col A B E` `A \<noteq> E`] .
		have "col A E B" using collinearorder[OF `axioms` `col A B E`] by blast
		have "E = E" using equalityreflexiveE[OF `axioms`] .
		have "col A E E" using col_b `axioms` `E = E` by blast
		have "B \<noteq> E" using betweennotequal[OF `axioms` `bet A B E`] by blast
		have "\<not> col B E C" using NChelper[OF `axioms` `\<not> col A E C` `col A E B` `col A E E` `B \<noteq> E`] .
		have "\<not> col C E B" using NCorder[OF `axioms` `\<not> col B E C`] by blast
		obtain J where "bet B J E \<and> bet C D J" using Pasch-outerE[OF `axioms` `bet B D F` `bet C F E` `\<not> col C E B`]  by  blast
		have "bet B J E" using `bet B J E \<and> bet C D J` by blast
		have "bet A B E" using `bet A B E` .
		have "bet A J E" using n3_5b[OF `axioms` `bet A B E` `bet B J E`] .
		have "\<not> col A C B" using parallelNC[OF `axioms` `parallel A C B D`] by blast
		have "\<not> col A B C" using NCorder[OF `axioms` `\<not> col A C B`] by blast
		have "col A J E" using col_b `axioms` `bet A J E` by blast
		have "col E A B" using collinearorder[OF `axioms` `col A B E`] by blast
		have "col E A J" using collinearorder[OF `axioms` `col A J E`] by blast
		have "A \<noteq> E" using betweennotequal[OF `axioms` `bet A B E`] by blast
		have "E \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> E`] .
		have "col A B J" using collinear4[OF `axioms` `col E A B` `col E A J` `E \<noteq> A`] .
		have "A \<noteq> J" using betweennotequal[OF `axioms` `bet A J E`] by blast
		have "\<not> col A J C" using NChelper[OF `axioms` `\<not> col A B C` `col A B A` `col A B J` `A \<noteq> J`] .
		have "bet B J E" using `bet B J E` .
		have "bet A B E" using `bet A B E` .
		have "bet A B J" using innertransitivityE[OF `axioms` `bet A B E` `bet B J E`] .
		have "bet C D J" using `bet B J E \<and> bet C D J` by blast
		obtain M where "bet A M D \<and> bet C M B" using Pasch-innerE[OF `axioms` `bet A B J` `bet C D J` `\<not> col A J C`]  by  blast
		have "bet A M D" using `bet A M D \<and> bet C M B` by blast
		have "bet C M B" using `bet A M D \<and> bet C M B` by blast
		have "bet B M C" using betweennesssymmetryE[OF `axioms` `bet C M B`] .
		have "bet A M D \<and> bet B M C" using `bet A M D \<and> bet C M B` `bet B M C` by blast
		have "cross A D B C" sorry
	next
		case 6
		have "bet D F B" using betweennesssymmetryE[OF `axioms` `bet B F D`] .
		have "bet E B A" using betweennesssymmetryE[OF `axioms` `bet A B E`] .
		have "\<not> col A B D" using parallelNC[OF `axioms` `parallel A C B D`] by blast
		have "col A B E" using col_b `axioms` `bet A B E \<and> seg_eq B E A B` by blast
		have "A = A" using equalityreflexiveE[OF `axioms`] .
		have "col A B A" using col_b `axioms` `A = A` by blast
		have "A \<noteq> E" using betweennotequal[OF `axioms` `bet A B E`] by blast
		have "\<not> col A E D" using NChelper[OF `axioms` `\<not> col A B D` `col A B A` `col A B E` `A \<noteq> E`] .
		have "\<not> col E A D" using NCorder[OF `axioms` `\<not> col A E D`] by blast
		obtain Q where "bet D Q A \<and> bet E F Q" using Pasch-outerE[OF `axioms` `bet D F B` `bet E B A` `\<not> col E A D`]  by  blast
		have "bet D Q A" using `bet D Q A \<and> bet E F Q` by blast
		have "bet E F Q" using `bet D Q A \<and> bet E F Q` by blast
		have "bet E F C" using betweennesssymmetryE[OF `axioms` `bet C F E`] .
		have "col E F Q" using col_b `axioms` `bet D Q A \<and> bet E F Q` by blast
		have "col E F C" using col_b `axioms` `bet E F C` by blast
		have "F \<noteq> E" using betweennotequal[OF `axioms` `bet C F E`] by blast
		have "E \<noteq> F" using inequalitysymmetric[OF `axioms` `F \<noteq> E`] .
		have "col F Q C" using collinear4[OF `axioms` `col E F Q` `col E F C` `E \<noteq> F`] .
		have "col F C Q" using collinearorder[OF `axioms` `col F Q C`] by blast
		have "bet A Q D" using betweennesssymmetryE[OF `axioms` `bet D Q A`] .
		have "parallel A C B D" using `parallel A C B D` .
		have "col B F D" using col_b `axioms` `bet B F D` by blast
		have "col B D F" using collinearorder[OF `axioms` `col B F D`] by blast
		have "F \<noteq> D" using betweennotequal[OF `axioms` `bet B F D`] by blast
		have "parallel A C F D" using collinearparallel[OF `axioms` `parallel A C B D` `col B D F` `F \<noteq> D`] .
		have "\<not> (meets A C F D)" sorry
		have "C = C" using equalityreflexiveE[OF `axioms`] .
		have "F = F" using equalityreflexiveE[OF `axioms`] .
		have "col A C C" using col_b `axioms` `C = C` by blast
		have "col F F D" using col_b `axioms` `F = F` by blast
		have "A \<noteq> C" using `A \<noteq> C` .
		have "F \<noteq> D" using `F \<noteq> D` .
		have "col C F Q" using collinearorder[OF `axioms` `col F C Q`] by blast
		have "bet C Q F" using collinearbetween[OF `axioms` `col A C C` `col F F D` `A \<noteq> C` `F \<noteq> D` `A \<noteq> C` `F \<noteq> D` `\<not> (meets A C F D)` `bet A Q D` `col C F Q`] .
		have "\<not> col A C B" using parallelNC[OF `axioms` `parallel A C B D`] by blast
		have "\<not> col A B C" using NCorder[OF `axioms` `\<not> col A C B`] by blast
		have "col A B A" using col_b `axioms` `A = A` by blast
		have "col A B E" using col_b `axioms` `bet A B E \<and> seg_eq B E A B` by blast
		have "A \<noteq> E" using betweennotequal[OF `axioms` `bet A B E`] by blast
		have "\<not> col A E C" using NChelper[OF `axioms` `\<not> col A B C` `col A B A` `col A B E` `A \<noteq> E`] .
		have "bet A B E" using `bet A B E` .
		have "bet C Q E" using n3_6b[OF `axioms` `bet C Q F` `bet C F E`] .
		obtain M where "bet A M Q \<and> bet C M B" using Pasch-innerE[OF `axioms` `bet A B E` `bet C Q E` `\<not> col A E C`]  by  blast
		have "bet A M Q" using `bet A M Q \<and> bet C M B` by blast
		have "bet C M B" using `bet A M Q \<and> bet C M B` by blast
		have "bet A M D" using n3_6b[OF `axioms` `bet A M Q` `bet A Q D`] .
		have "bet B M C" using betweennesssymmetryE[OF `axioms` `bet C M B`] .
		have "cross A D B C" sorry
	next
	thus ?thesis by blast
qed

end