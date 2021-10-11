theory Prop35
	imports n3_6a n3_7b EFreflexive Geometry NCdistinct NChelper NCorder Prop34 Prop35A betweennotequal collinear4 collinearorder congruenceflip congruencesymmetric congruencetransitive diagonalsmeet equalitysymmetric inequalitysymmetric lessthancongruence lessthancongruence2 lessthantransitive oppositesidesymmetric parallelNC parallelPasch paralleldef2B parallelflip parallelsymmetric planeseparation trichotomy2
begin

theorem(in euclidean_geometry) Prop35:
	assumes 
		"parallelogram A B C D"
		"parallelogram E B C F"
		"col A D E"
		"col A D F"
	shows "qua_eq_area A B C D E B C F"
proof -
	have "parallel A B C D \<and> parallel A D B C" using parallelogram_f[OF `parallelogram A B C D`] .
	have "parallel E B C F \<and> parallel E F B C" using parallelogram_f[OF `parallelogram E B C F`] .
	have "parallel A B C D" using `parallel A B C D \<and> parallel A D B C` by blast
	have "parallel A D B C" using `parallel A B C D \<and> parallel A D B C` by blast
	have "parallel E B C F" using `parallel E B C F \<and> parallel E F B C` by blast
	have "parallel E F B C" using `parallel E B C F \<and> parallel E F B C` by blast
	have "parallel A B D C" using parallelflip[OF `parallel A B C D`] by blast
	have "parallel E B F C" using parallelflip[OF `parallel E B C F`] by blast
	have "parallel F C E B" using parallelsymmetric[OF `parallel E B F C`] .
	have "seg_eq A D B C" using Prop34[OF `parallelogram A B C D`] by blast
	have "seg_eq E F B C" using Prop34[OF `parallelogram E B C F`] by blast
	have "seg_eq B C E F" using congruencesymmetric[OF `seg_eq E F B C`] .
	have "seg_eq A D E F" using congruencetransitive[OF `seg_eq A D B C` `seg_eq B C E F`] .
	have "A \<noteq> D" using parallel_f[OF `parallel A D B C`] by fastforce
	have "E \<noteq> F" using parallel_f[OF `parallel E F B C`] by fastforce
	have "D \<noteq> A" using inequalitysymmetric[OF `A \<noteq> D`] .
	have "\<not> (\<not> (qua_eq_area A B C D E B C F))"
	proof (rule ccontr)
		assume "\<not> (\<not> (\<not> (qua_eq_area A B C D E B C F)))"
hence "\<not> (qua_eq_area A B C D E B C F)" by blast
		have "\<not> (bet A D F)"
		proof (rule ccontr)
			assume "\<not> (\<not> (bet A D F))"
hence "bet A D F" by blast
			have "col A D F" using collinear_b `bet A D F` by blast
			have "col A D E" using `col A D E` .
			have "col D A F" using collinearorder[OF `col A D F`] by blast
			have "col D A E" using collinearorder[OF `col A D E`] by blast
			have "col A F E" using collinear4[OF `col D A F` `col D A E` `D \<noteq> A`] .
			have "col A E F" using collinearorder[OF `col A F E`] by blast
			have "qua_eq_area A B C D E B C F" using Prop35A[OF `parallelogram A B C D` `parallelogram E B C F` `bet A D F` `col A E F`] .
			show "False" using `qua_eq_area A B C D E B C F` `\<not> (qua_eq_area A B C D E B C F)` by blast
		qed
		hence "\<not> (bet A D F)" by blast
		have "\<not> (bet A D E)"
		proof (rule ccontr)
			assume "\<not> (\<not> (bet A D E))"
hence "bet A D E" by blast
			obtain H where "bet B H E \<and> bet C H D" using parallelPasch[OF `parallelogram A B C D` `bet A D E`]  by  blast
			have "bet B H E" using `bet B H E \<and> bet C H D` by blast
			have "bet C H D" using `bet B H E \<and> bet C H D` by blast
			have "bet D H C" using betweennesssymmetryE[OF `bet C H D`] .
			have "col B H E" using collinear_b `bet B H E \<and> bet C H D` by blast
			have "col B E H" using collinearorder[OF `col B H E`] by blast
			have "\<not> col A D B" using parallelNC[OF `parallel A D B C`] by blast
			have "col A D E" using collinear_b `bet A D E` by blast
			have "D = D" using equalityreflexiveE.
			have "col A D D" using collinear_b `D = D` by blast
			have "D \<noteq> E" using betweennotequal[OF `bet A D E`] by blast
			have "\<not> col D E B" using NChelper[OF `\<not> col A D B` `col A D D` `col A D E` `D \<noteq> E`] .
			have "\<not> col B E D" using NCorder[OF `\<not> col D E B`] by blast
			have "bet D H C \<and> col B E H \<and> \<not> col B E D" using `bet D H C` `col B E H` `\<not> col B E D` by blast
			have "oppo_side D B E C" using oppositeside_b[OF `bet D H C` `col B E H` `\<not> col B E D`] .
			have "oppo_side C B E D" using oppositesidesymmetric[OF `oppo_side D B E C`] .
			have "parallel F C B E" using parallelflip[OF `parallel F C E B`] by blast
			have "parallel B E F C" using parallelsymmetric[OF `parallel F C B E`] .
			have "tarski_parallel B E F C" using paralleldef2B[OF `parallel B E F C`] .
			have "same_side F C B E" using tarski_parallel_f[OF `tarski_parallel B E F C`] by blast
			have "oppo_side F B E D" using planeseparation[OF `same_side F C B E` `oppo_side C B E D`] .
			obtain e where "bet F e D \<and> col B E e \<and> \<not> col B E F" using oppositeside_f[OF `oppo_side F B E D`]  by  blast
			have "bet F e D" using `bet F e D \<and> col B E e \<and> \<not> col B E F` by blast
			have "F \<noteq> D" using betweennotequal[OF `bet F e D`] by blast
			have "col F e D" using collinear_b `bet F e D \<and> col B E e \<and> \<not> col B E F` by blast
			have "\<not> (e \<noteq> E)"
			proof (rule ccontr)
				assume "\<not> (\<not> (e \<noteq> E))"
hence "e \<noteq> E" by blast
				have "col B E e" using `bet F e D \<and> col B E e \<and> \<not> col B E F` by blast
				have "col A D E" using `col A D E` .
				have "col A D F" using `col A D F` .
				have "A \<noteq> D" using betweennotequal[OF `bet A D E`] by blast
				have "col D E F" using collinear4[OF `col A D E` `col A D F` `A \<noteq> D`] .
				have "col F D E" using collinearorder[OF `col D E F`] by blast
				have "col F D e" using collinearorder[OF `col F e D`] by blast
				have "col D E e" using collinear4[OF `col F D E` `col F D e` `F \<noteq> D`] .
				have "col e E D" using collinearorder[OF `col D E e`] by blast
				have "col e E B" using collinearorder[OF `col B E e`] by blast
				have "col E D B" using collinear4[OF `col e E D` `col e E B` `e \<noteq> E`] .
				have "col B E D" using collinearorder[OF `col E D B`] by blast
				have "\<not> col B E D" using `\<not> col B E D` .
				show "False" using `\<not> col B E D` `col B E D` by blast
			qed
			hence "e = E" by blast
			have "bet F E D" using `bet F e D` `e = E` by blast
			have "bet D E F" using betweennesssymmetryE[OF `bet F E D`] .
			have "bet A D E" using `bet A D E` .
			have "bet A D F" using n3_7b[OF `bet A D E` `bet D E F`] .
			have "\<not> (bet A D F)" using `\<not> (bet A D F)` .
			show "False" using `\<not> (bet A D F)` `bet A D F` by blast
		qed
		hence "\<not> (bet A D E)" by blast
		have "parallel B A D C" using parallelflip[OF `parallel A B C D`] by blast
		have "parallel D C B A" using parallelsymmetric[OF `parallel B A D C`] .
		have "parallel D A C B" using parallelflip[OF `parallel A D B C`] by blast
		have "parallelogram D C B A" using parallelogram_b[OF `parallel D C B A` `parallel D A C B`] .
		have "parallel B E F C" using parallelflip[OF `parallel E B C F`] by blast
		have "parallel F C B E" using parallelsymmetric[OF `parallel B E F C`] .
		have "parallel F E C B" using parallelflip[OF `parallel E F B C`] by blast
		have "parallelogram F C B E" using parallelogram_b[OF `parallel F C B E` `parallel F E C B`] .
		have "\<not> (bet E A D)"
		proof (rule ccontr)
			assume "\<not> (\<not> (bet E A D))"
hence "bet E A D" by blast
			have "bet D A E" using betweennesssymmetryE[OF `bet E A D`] .
			have "col D A E" using collinear_b `bet D A E` by blast
			have "col A D E" using collinearorder[OF `col D A E`] by blast
			have "A \<noteq> D" using betweennotequal[OF `bet E A D`] by blast
			have "col D E F" using collinear4[OF `col A D E` `col A D F` `A \<noteq> D`] .
			have "col D F E" using collinearorder[OF `col D E F`] by blast
			have "qua_eq_area D C B A F C B E" using Prop35A[OF `parallelogram D C B A` `parallelogram F C B E` `bet D A E` `col D F E`] .
			have "qua_eq_area D C B A E B C F" using EFpermutationE[OF `qua_eq_area D C B A F C B E`] by blast
			have "qua_eq_area E B C F D C B A" using EFsymmetricE[OF `qua_eq_area D C B A E B C F`] .
			have "qua_eq_area E B C F A B C D" using EFpermutationE[OF `qua_eq_area E B C F D C B A`] by blast
			have "qua_eq_area A B C D E B C F" using EFsymmetricE[OF `qua_eq_area E B C F A B C D`] .
			show "False" using `qua_eq_area A B C D E B C F` `\<not> (qua_eq_area A B C D E B C F)` by blast
		qed
		hence "\<not> (bet E A D)" by blast
		have "\<not> (bet D A F)"
		proof (rule ccontr)
			assume "\<not> (\<not> (bet D A F))"
hence "bet D A F" by blast
			obtain H where "bet C H F \<and> bet B H A" using parallelPasch[OF `parallelogram D C B A` `bet D A F`]  by  blast
			have "bet C H F" using `bet C H F \<and> bet B H A` by blast
			have "bet B H A" using `bet C H F \<and> bet B H A` by blast
			have "bet A H B" using betweennesssymmetryE[OF `bet B H A`] .
			have "col C H F" using collinear_b `bet C H F \<and> bet B H A` by blast
			have "col C F H" using collinearorder[OF `col C H F`] by blast
			have "\<not> col D A C" using parallelNC[OF `parallel D A C B`] by blast
			have "col D A F" using collinear_b `bet D A F` by blast
			have "A = A" using equalityreflexiveE.
			have "col D A A" using collinear_b `A = A` by blast
			have "A \<noteq> F" using betweennotequal[OF `bet D A F`] by blast
			have "\<not> col A F C" using NChelper[OF `\<not> col D A C` `col D A A` `col D A F` `A \<noteq> F`] .
			have "\<not> col C F A" using NCorder[OF `\<not> col A F C`] by blast
			have "bet A H B \<and> col C F H \<and> \<not> col C F A" using `bet A H B` `col C F H` `\<not> col C F A` by blast
			have "oppo_side A C F B" using oppositeside_b[OF `bet A H B` `col C F H` `\<not> col C F A`] .
			have "oppo_side B C F A" using oppositesidesymmetric[OF `oppo_side A C F B`] .
			have "parallel E B C F" using parallelflip[OF `parallel B E F C`] by blast
			have "parallel C F E B" using parallelsymmetric[OF `parallel E B C F`] .
			have "tarski_parallel C F E B" using paralleldef2B[OF `parallel C F E B`] .
			have "same_side E B C F" using tarski_parallel_f[OF `tarski_parallel C F E B`] by blast
			have "oppo_side E C F A" using planeseparation[OF `same_side E B C F` `oppo_side B C F A`] .
			obtain e where "bet E e A \<and> col C F e \<and> \<not> col C F E" using oppositeside_f[OF `oppo_side E C F A`]  by  blast
			have "bet E e A" using `bet E e A \<and> col C F e \<and> \<not> col C F E` by blast
			have "E \<noteq> A" using betweennotequal[OF `bet E e A`] by blast
			have "\<not> (e \<noteq> F)"
			proof (rule ccontr)
				assume "\<not> (\<not> (e \<noteq> F))"
hence "e \<noteq> F" by blast
				have "col C F e" using `bet E e A \<and> col C F e \<and> \<not> col C F E` by blast
				have "col D A F" using `col D A F` .
				have "col D A E" using collinearorder[OF `col A D E`] by blast
				have "D \<noteq> A" using betweennotequal[OF `bet D A F`] by blast
				have "col A F E" using collinear4[OF `col D A F` `col D A E` `D \<noteq> A`] .
				have "col E A F" using collinearorder[OF `col A F E`] by blast
				have "col E e A" using collinear_b `bet E e A \<and> col C F e \<and> \<not> col C F E` by blast
				have "col E A e" using collinearorder[OF `col E e A`] by blast
				have "col A F e" using collinear4[OF `col E A F` `col E A e` `E \<noteq> A`] .
				have "col e F A" using collinearorder[OF `col A F e`] by blast
				have "col e F C" using collinearorder[OF `col C F e`] by blast
				have "col F A C" using collinear4[OF `col e F A` `col e F C` `e \<noteq> F`] .
				have "col C F A" using collinearorder[OF `col F A C`] by blast
				have "\<not> col C F A" using `\<not> col C F A` .
				show "False" using `\<not> col C F A` `col C F A` by blast
			qed
			hence "e = F" by blast
			have "bet E F A" using `bet E e A` `e = F` by blast
			have "bet A F E" using betweennesssymmetryE[OF `bet E F A`] .
			have "bet D A F" using `bet D A F` .
			have "bet D A E" using n3_7b[OF `bet D A F` `bet A F E`] .
			have "bet E A D" using betweennesssymmetryE[OF `bet D A E`] .
			have "\<not> (bet E A D)" using `\<not> (bet E A D)` .
			show "False" using `\<not> (bet E A D)` `bet E A D` by blast
		qed
		hence "\<not> (bet D A F)" by blast
		have "col A D F" using `col A D F` .
		have "A = D \<or> A = F \<or> D = F \<or> bet D A F \<or> bet A D F \<or> bet A F D" using collinear_f[OF `col A D F`] .
		have "col A D E" using `col A D E` .
		have "A = D \<or> A = E \<or> D = E \<or> bet D A E \<or> bet A D E \<or> bet A E D" using collinear_f[OF `col A D E`] .
		have "\<not> (A = F)"
		proof (rule ccontr)
			assume "\<not> (A \<noteq> F)"
			hence "A = F" by blast
			have "F = D \<or> F = E \<or> D = E \<or> bet D A E \<or> bet A D E \<or> bet A E D" using `A = D \<or> A = E \<or> D = E \<or> bet D A E \<or> bet A D E \<or> bet A E D` `A = F` `A = F` by blast
			consider "F = D"|"F = E"|"D = E"|"bet D A E"|"bet A D E"|"bet A E D" using `F = D \<or> F = E \<or> D = E \<or> bet D A E \<or> bet A D E \<or> bet A E D`  by blast
			hence "A \<noteq> F"
			proof (cases)
				assume "F = D"
				have "A = D" using `A = F` `F = D` by blast
				have "\<not> (A = F)"
				proof (rule ccontr)
					assume "\<not> (A \<noteq> F)"
					hence "A = F" by blast
					have "A \<noteq> D" using `A \<noteq> D` .
					show "False" using `A \<noteq> D` `A = D` by blast
				qed
				hence "A \<noteq> F" by blast
				thus ?thesis by blast
			next
				assume "F = E"
				have "\<not> (A = F)"
				proof (rule ccontr)
					assume "\<not> (A \<noteq> F)"
					hence "A = F" by blast
					have "E \<noteq> F" using `E \<noteq> F` .
					have "F \<noteq> E" using inequalitysymmetric[OF `E \<noteq> F`] .
					show "False" using `F \<noteq> E` `F = E` by blast
				qed
				hence "A \<noteq> F" by blast
				thus ?thesis by blast
			next
				assume "D = E"
				have "\<not> (A = F)"
				proof (rule ccontr)
					assume "\<not> (A \<noteq> F)"
					hence "A = F" by blast
					obtain p where "bet E p C \<and> bet B p F" using diagonalsmeet[OF `parallelogram E B C F`]  by  blast
					have "bet E p C" using `bet E p C \<and> bet B p F` by blast
					have "bet B p F" using `bet E p C \<and> bet B p F` by blast
					have "col E p C" using collinear_b `bet E p C \<and> bet B p F` by blast
					have "col B p F" using collinear_b `bet E p C \<and> bet B p F` by blast
					have "col F B p" using collinearorder[OF `col B p F`] by blast
					have "col E C p" using collinearorder[OF `col E p C`] by blast
					have "\<not> col E F C" using parallelNC[OF `parallel B E F C`] by blast
					have "E \<noteq> C" using NCdistinct[OF `\<not> col E F C`] by blast
					have "\<not> col E F B" using parallelNC[OF `parallel E F B C`] by blast
					have "F \<noteq> B" using NCdistinct[OF `\<not> col E F B`] by blast
					have "E \<noteq> C \<and> F \<noteq> B \<and> col E C p \<and> col F B p" using `E \<noteq> C` `F \<noteq> B` `col E C p` `col F B p` by blast
					have "meets E C F B" using meet_b[OF `E \<noteq> C` `F \<noteq> B` `col E C p` `col F B p`] .
					have "meets D C F B" using `meets E C F B` `D = E` by blast
					have "meets D C A B" using `meets D C F B` `A = F` by blast
					have "parallel D C A B" using parallelsymmetric[OF `parallel A B D C`] .
					have "\<not> (meets D C A B)" using parallel_f[OF `parallel D C A B`] by fastforce
					show "False" using `\<not> (meets D C A B)` `meets D C A B` by blast
				qed
				hence "A \<noteq> F" by blast
				thus ?thesis by blast
			next
				assume "bet D A E"
				have "\<not> (A = F)"
				proof (rule ccontr)
					assume "\<not> (A \<noteq> F)"
					hence "A = F" by blast
					have "bet E A D" using betweennesssymmetryE[OF `bet D A E`] .
					have "\<not> (bet E A D)" using `\<not> (bet E A D)` .
					show "False" using `\<not> (bet E A D)` `bet E A D` by blast
				qed
				hence "A \<noteq> F" by blast
				thus ?thesis by blast
			next
				assume "bet A D E"
				have "\<not> (A = F)"
				proof (rule ccontr)
					assume "\<not> (A \<noteq> F)"
					hence "A = F" by blast
					have "\<not> (bet A D E)" using `\<not> (bet A D E)` .
					show "False" using `\<not> (bet A D E)` `bet A D E` by blast
				qed
				hence "A \<noteq> F" by blast
				thus ?thesis by blast
			next
				assume "bet A E D"
				have "\<not> (A = F)"
				proof (rule ccontr)
					assume "\<not> (A \<noteq> F)"
					hence "A = F" by blast
					have "seg_eq A E A E" using congruencereflexiveE.
					have "seg_eq F E A E" using `seg_eq A E A E` `A = F` by blast
					have "seg_eq A E F E" using congruencesymmetric[OF `seg_eq F E A E`] .
					have "seg_lt F E A D" using lessthan_b[OF `bet A E D` `seg_eq A E F E`] .
					have "seg_eq A D E F" using `seg_eq A D E F` .
					have "seg_lt F E E F" using lessthancongruence[OF `seg_lt F E A D` `seg_eq A D E F`] .
					have "seg_eq E F F E" using equalityreverseE.
					have "seg_lt F E F E" using lessthancongruence[OF `seg_lt F E E F` `seg_eq E F F E`] .
					have "\<not> (seg_lt F E F E)" using trichotomy2[OF `seg_lt F E F E`] .
					show "False" using `\<not> (seg_lt F E F E)` `seg_lt F E F E` by blast
				qed
				hence "A \<noteq> F" by blast
				thus ?thesis by blast
			qed
			show "False" using `A \<noteq> F` `A = F` by blast
		qed
		hence "A \<noteq> F" by blast
		have "\<not> (D = F)"
		proof (rule ccontr)
			assume "\<not> (D \<noteq> F)"
			hence "D = F" by blast
			have "A = F \<or> A = E \<or> F = E \<or> bet D A E \<or> bet A D E \<or> bet A E D" using `A = D \<or> A = E \<or> D = E \<or> bet D A E \<or> bet A D E \<or> bet A E D` `D = F` `D = F` by blast
			consider "A = F"|"A = E"|"F = E"|"bet D A E"|"bet A D E"|"bet A E D" using `A = F \<or> A = E \<or> F = E \<or> bet D A E \<or> bet A D E \<or> bet A E D`  by blast
			hence "D \<noteq> F"
			proof (cases)
				assume "A = F"
				have "\<not> (D = F)"
				proof (rule ccontr)
					assume "\<not> (D \<noteq> F)"
					hence "D = F" by blast
					have "A \<noteq> F" using `A \<noteq> F` .
					show "False" using `A \<noteq> F` `A = F` by blast
				qed
				hence "D \<noteq> F" by blast
				thus ?thesis by blast
			next
				assume "A = E"
				have "\<not> (D = F)"
				proof (rule ccontr)
					assume "\<not> (D \<noteq> F)"
					hence "D = F" by blast
					obtain M where "bet A M C \<and> bet B M D" using diagonalsmeet[OF `parallelogram A B C D`]  by  blast
					have "bet A M C" using `bet A M C \<and> bet B M D` by blast
					have "bet B M D" using `bet A M C \<and> bet B M D` by blast
					have "\<not> (col A B C)"
					proof (rule ccontr)
						assume "\<not> (\<not> (col A B C))"
hence "col A B C" by blast
						have "C = C" using equalityreflexiveE.
						have "col C D C" using collinear_b `C = C` by blast
						have "A \<noteq> B" using parallel_f[OF `parallel A B C D`] by fastforce
						have "C \<noteq> D" using parallel_f[OF `parallel A B C D`] by fastforce
						have "meets A B C D" using meet_b[OF `A \<noteq> B` `C \<noteq> D` `col A B C` `col C D C`] .
						have "\<not> (meets A B C D)" using parallel_f[OF `parallel A B C D`] by fastforce
						show "False" using `\<not> (meets A B C D)` `meets A B C D` by blast
					qed
					hence "\<not> col A B C" by blast
					have "qua_eq_area A B C D A B C D" using EFreflexive[OF `bet A M C` `bet B M D` `\<not> col A B C`] .
					have "qua_eq_area A B C D E B C D" using `qua_eq_area A B C D A B C D` `A = E` by blast
					have "qua_eq_area A B C D E B C F" using `qua_eq_area A B C D A B C D` `A = E` `D = F` by blast
					show "False" using `qua_eq_area A B C D E B C F` `\<not> (qua_eq_area A B C D E B C F)` by blast
				qed
				hence "D \<noteq> F" by blast
				thus ?thesis by blast
			next
				assume "F = E"
				have "\<not> (D = F)"
				proof (rule ccontr)
					assume "\<not> (D \<noteq> F)"
					hence "D = F" by blast
					have "F = E" using `D = F` `D = F` `F = E` by blast
					have "E = F" using equalitysymmetric[OF `F = E`] .
					show "False" using `E = F` `E \<noteq> F` by blast
				qed
				hence "D \<noteq> F" by blast
				thus ?thesis by blast
			next
				assume "bet D A E"
				have "\<not> (D = F)"
				proof (rule ccontr)
					assume "\<not> (D \<noteq> F)"
					hence "D = F" by blast
					have "bet E A D" using betweennesssymmetryE[OF `bet D A E`] .
					have "\<not> (bet E A D)" using `\<not> (bet E A D)` .
					show "False" using `\<not> (bet E A D)` `bet E A D` by blast
				qed
				hence "D \<noteq> F" by blast
				thus ?thesis by blast
			next
				assume "bet A D E"
				have "\<not> (D = F)"
				proof (rule ccontr)
					assume "\<not> (D \<noteq> F)"
					hence "D = F" by blast
					have "\<not> (bet A D E)" using `\<not> (bet A D E)` .
					show "False" using `\<not> (bet A D E)` `bet A D E` by blast
				qed
				hence "D \<noteq> F" by blast
				thus ?thesis by blast
			next
				assume "bet A E D"
				have "\<not> (D = F)"
				proof (rule ccontr)
					assume "\<not> (D \<noteq> F)"
					hence "D = F" by blast
					have "bet D E A" using betweennesssymmetryE[OF `bet A E D`] .
					have "seg_eq D E D E" using congruencereflexiveE.
					have "seg_lt D E D A" using lessthan_b[OF `bet D E A` `seg_eq D E D E`] .
					have "seg_eq D E F E" using `seg_eq D E D E` `D = F` by blast
					have "seg_lt F E D A" using lessthancongruence2[OF `seg_lt D E D A` `seg_eq D E F E`] .
					have "seg_eq F E E F" using equalityreverseE.
					have "seg_lt E F D A" using lessthancongruence2[OF `seg_lt F E D A` `seg_eq F E E F`] .
					have "seg_eq D A A D" using equalityreverseE.
					have "seg_lt E F A D" using lessthancongruence[OF `seg_lt E F D A` `seg_eq D A A D`] .
					have "seg_eq A D E F" using `seg_eq A D E F` .
					have "seg_lt E F E F" using lessthancongruence[OF `seg_lt E F A D` `seg_eq A D E F`] .
					have "\<not> (seg_lt E F E F)" using trichotomy2[OF `seg_lt E F E F`] .
					show "False" using `\<not> (seg_lt E F E F)` `seg_lt E F E F` by blast
				qed
				hence "D \<noteq> F" by blast
				thus ?thesis by blast
			qed
			show "False" using `D \<noteq> F` `D = F` by blast
		qed
		hence "D \<noteq> F" by blast
		consider "A = D"|"A = F"|"D = F"|"bet D A F"|"bet A D F"|"bet A F D" using `A = D \<or> A = F \<or> D = F \<or> bet D A F \<or> bet A D F \<or> bet A F D`  by blast
		hence "bet A F D"
		proof (cases)
			assume "A = D"
			have "\<not> (\<not> (bet A F D))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (bet A F D)))"
hence "\<not> (bet A F D)" by blast
				have "A \<noteq> D" using `A \<noteq> D` .
				show "False" using `A \<noteq> D` `A = D` by blast
			qed
			hence "bet A F D" by blast
			thus ?thesis by blast
		next
			assume "A = F"
			have "\<not> (\<not> (bet A F D))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (bet A F D)))"
hence "\<not> (bet A F D)" by blast
				have "A \<noteq> F" using `A \<noteq> F` .
				show "False" using `A \<noteq> F` `A = F` by blast
			qed
			hence "bet A F D" by blast
			thus ?thesis by blast
		next
			assume "D = F"
			have "\<not> (\<not> (bet A F D))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (bet A F D)))"
hence "\<not> (bet A F D)" by blast
				have "D \<noteq> F" using `D \<noteq> F` .
				show "False" using `D \<noteq> F` `D = F` by blast
			qed
			hence "bet A F D" by blast
			thus ?thesis by blast
		next
			assume "bet D A F"
			have "\<not> (\<not> (bet A F D))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (bet A F D)))"
hence "\<not> (bet A F D)" by blast
				have "\<not> (bet D A F)" using `\<not> (bet D A F)` .
				show "False" using `\<not> (bet D A F)` `bet D A F` by blast
			qed
			hence "bet A F D" by blast
			thus ?thesis by blast
		next
			assume "bet A D F"
			have "\<not> (\<not> (bet A F D))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (bet A F D)))"
hence "\<not> (bet A F D)" by blast
				have "\<not> (bet A D F)" using `\<not> (bet A D F)` .
				show "False" using `\<not> (bet A D F)` `bet A D F` by blast
			qed
			hence "bet A F D" by blast
			thus ?thesis by blast
		next
			assume "bet A F D"
			have "bet A F D" using `bet A F D` .
			thus ?thesis by blast
		qed
		consider "A = D"|"A = E"|"D = E"|"bet D A E"|"bet A D E"|"bet A E D" using `A = D \<or> A = E \<or> D = E \<or> bet D A E \<or> bet A D E \<or> bet A E D`  by blast
		hence "bet A E D"
		proof (cases)
			assume "A = D"
			have "\<not> (\<not> (bet A E D))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (bet A E D)))"
hence "\<not> (bet A E D)" by blast
				have "A \<noteq> D" using `A \<noteq> D` .
				show "False" using `A \<noteq> D` `A = D` by blast
			qed
			hence "bet A E D" by blast
			thus ?thesis by blast
		next
			assume "A = E"
			have "\<not> (\<not> (bet A E D))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (bet A E D)))"
hence "\<not> (bet A E D)" by blast
				have "bet A F D" using `bet A F D` .
				have "seg_eq A F A F" using congruencereflexiveE.
				have "seg_eq A F E F" using `seg_eq A F A F` `A = E` by blast
				have "seg_lt E F A D" using lessthan_b[OF `bet A F D` `seg_eq A F E F`] .
				have "seg_eq A D E F" using `seg_eq A D E F` .
				have "seg_lt E F E F" using lessthancongruence[OF `seg_lt E F A D` `seg_eq A D E F`] .
				have "\<not> (seg_lt E F E F)" using trichotomy2[OF `seg_lt E F E F`] .
				show "False" using `\<not> (seg_lt E F E F)` `seg_lt E F E F` by blast
			qed
			hence "bet A E D" by blast
			thus ?thesis by blast
		next
			assume "D = E"
			have "\<not> (\<not> (bet A E D))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (bet A E D)))"
hence "\<not> (bet A E D)" by blast
				have "bet D F A" using betweennesssymmetryE[OF `bet A F D`] .
				have "seg_eq D F D F" using congruencereflexiveE.
				have "seg_lt D F D A" using lessthan_b[OF `bet D F A` `seg_eq D F D F`] .
				have "seg_lt E F D A" using `seg_lt D F D A` `D = E` by blast
				have "seg_eq D A E F" using congruenceflip[OF `seg_eq A D E F`] by blast
				have "seg_lt E F E F" using lessthancongruence[OF `seg_lt E F D A` `seg_eq D A E F`] .
				have "\<not> (seg_lt E F E F)" using trichotomy2[OF `seg_lt E F E F`] .
				show "False" using `\<not> (seg_lt E F E F)` `seg_lt E F E F` by blast
			qed
			hence "bet A E D" by blast
			thus ?thesis by blast
		next
			assume "bet D A E"
			have "\<not> (\<not> (bet A E D))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (bet A E D)))"
hence "\<not> (bet A E D)" by blast
				have "bet E A D" using betweennesssymmetryE[OF `bet D A E`] .
				have "\<not> (bet E A D)" using `\<not> (bet E A D)` .
				show "False" using `\<not> (bet E A D)` `bet E A D` by blast
			qed
			hence "bet A E D" by blast
			thus ?thesis by blast
		next
			assume "bet A D E"
			have "\<not> (\<not> (bet A E D))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (bet A E D)))"
hence "\<not> (bet A E D)" by blast
				have "\<not> (bet A D E)" using `\<not> (bet A D E)` .
				show "False" using `\<not> (bet A D E)` `bet A D E` by blast
			qed
			hence "bet A E D" by blast
			thus ?thesis by blast
		next
			assume "bet A E D"
			have "bet A E D" using `bet A E D` .
			thus ?thesis by blast
		qed
		have "\<not> (bet A E F)"
		proof (rule ccontr)
			assume "\<not> (\<not> (bet A E F))"
hence "bet A E F" by blast
			have "bet E F D" using n3_6a[OF `bet A E F` `bet A F D`] .
			have "seg_eq E F E F" using congruencereflexiveE.
			have "seg_lt E F E D" using lessthan_b[OF `bet E F D` `seg_eq E F E F`] .
			have "bet A E D" using `bet A E D` .
			have "bet D E A" using betweennesssymmetryE[OF `bet A E D`] .
			have "seg_eq D E D E" using congruencereflexiveE.
			have "seg_lt D E D A" using lessthan_b[OF `bet D E A` `seg_eq D E D E`] .
			have "seg_eq E D D E" using equalityreverseE.
			have "seg_lt E F D E" using lessthancongruence[OF `seg_lt E F E D` `seg_eq E D D E`] .
			have "seg_lt E F D A" using lessthantransitive[OF `seg_lt E F D E` `seg_lt D E D A`] .
			have "seg_eq D A A D" using equalityreverseE.
			have "seg_lt E F A D" using lessthancongruence[OF `seg_lt E F D A` `seg_eq D A A D`] .
			have "seg_lt E F E F" using lessthancongruence[OF `seg_lt E F A D` `seg_eq A D E F`] .
			have "\<not> (seg_lt E F E F)" using trichotomy2[OF `seg_lt E F E F`] .
			show "False" using `\<not> (seg_lt E F E F)` `seg_lt E F E F` by blast
		qed
		hence "\<not> (bet A E F)" by blast
		have "\<not> (bet A F E)"
		proof (rule ccontr)
			assume "\<not> (\<not> (bet A F E))"
hence "bet A F E" by blast
			have "bet F E D" using n3_6a[OF `bet A F E` `bet A E D`] .
			have "seg_eq F E F E" using congruencereflexiveE.
			have "seg_lt F E F D" using lessthan_b[OF `bet F E D` `seg_eq F E F E`] .
			have "bet A F D" using `bet A F D` .
			have "bet D F A" using betweennesssymmetryE[OF `bet A F D`] .
			have "seg_eq D F D F" using congruencereflexiveE.
			have "seg_lt D F D A" using lessthan_b[OF `bet D F A` `seg_eq D F D F`] .
			have "seg_eq F D D F" using equalityreverseE.
			have "seg_lt F E D F" using lessthancongruence[OF `seg_lt F E F D` `seg_eq F D D F`] .
			have "seg_lt F E D A" using lessthantransitive[OF `seg_lt F E D F` `seg_lt D F D A`] .
			have "seg_eq D A A D" using equalityreverseE.
			have "seg_lt F E A D" using lessthancongruence[OF `seg_lt F E D A` `seg_eq D A A D`] .
			have "seg_eq A D F E" using congruenceflip[OF `seg_eq A D E F`] by blast
			have "seg_lt F E F E" using lessthancongruence[OF `seg_lt F E A D` `seg_eq A D F E`] .
			have "\<not> (seg_lt F E F E)" using trichotomy2[OF `seg_lt F E F E`] .
			show "False" using `\<not> (seg_lt F E F E)` `seg_lt F E F E` by blast
		qed
		hence "\<not> (bet A F E)" by blast
		have "E = F" using connectivityE[OF `bet A E D` `bet A F D` `\<not> (bet A E F)` `\<not> (bet A F E)`] .
		have "E \<noteq> F" using `E \<noteq> F` .
		show "False" using `E \<noteq> F` `E = F` by blast
	qed
	hence "qua_eq_area A B C D E B C F" by blast
	thus ?thesis by blast
qed

end