theory planeseparation
	imports n3_6b n3_7a n3_7b n9_5a n9_5b Geometry betweennotequal collinear4 collinear5 collinearorder equalitysymmetric inequalitysymmetric outerconnectivity twolines2
begin

theorem planeseparation:
	assumes "axioms"
		"same_side C D A B"
		"oppo_side D A B E"
	shows "oppo_side C A B E"
proof -
	obtain G H Q where "col A B G \<and> col A B H \<and> bet C G Q \<and> bet D H Q \<and> \<not> col A B C \<and> \<not> col A B D" using sameside_f[OF `axioms` `same_side C D A B`]  by  blast
	have "col A B G" using `col A B G \<and> col A B H \<and> bet C G Q \<and> bet D H Q \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "col A B H" using `col A B G \<and> col A B H \<and> bet C G Q \<and> bet D H Q \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "bet C G Q" using `col A B G \<and> col A B H \<and> bet C G Q \<and> bet D H Q \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "bet D H Q" using `col A B G \<and> col A B H \<and> bet C G Q \<and> bet D H Q \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "\<not> col A B C" using `col A B G \<and> col A B H \<and> bet C G Q \<and> bet D H Q \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> B)"
		hence "A = B" by blast
		have "col A B C" using collinear_b `axioms` `A = B` by blast
		show "False" using `col A B C` `col A B G \<and> col A B H \<and> bet C G Q \<and> bet D H Q \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	qed
	hence "A \<noteq> B" by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	obtain W where "bet D W E \<and> col A B W \<and> \<not> col A B D" using oppositeside_f[OF `axioms` `oppo_side D A B E`]  by  blast
	have "bet D W E" using `bet D W E \<and> col A B W \<and> \<not> col A B D` by blast
	have "C \<noteq> G" using betweennotequal[OF `axioms` `bet C G Q`] by blast
	have "G \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> G`] .
	have "G \<noteq> Q" using betweennotequal[OF `axioms` `bet C G Q`] by blast
	consider "col C Q D"|"\<not> col C Q D" by blast
	hence "oppo_side C A B E"
	proof (cases)
		assume "col C Q D"
		have "\<not> (\<not> (oppo_side C A B E))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (oppo_side C A B E)))"
hence "\<not> (oppo_side C A B E)" by blast
			have "col Q C D" using collinearorder[OF `axioms` `col C Q D`] by blast
			have "\<not> (G \<noteq> H)"
			proof (rule ccontr)
				assume "\<not> (\<not> (G \<noteq> H))"
hence "G \<noteq> H" by blast
				have "col A B G" using `col A B G` .
				have "col A B H" using `col A B H` .
				have "col C G Q" using collinear_b `axioms` `col A B G \<and> col A B H \<and> bet C G Q \<and> bet D H Q \<and> \<not> col A B C \<and> \<not> col A B D` by blast
				have "col D H Q" using collinear_b `axioms` `col A B G \<and> col A B H \<and> bet C G Q \<and> bet D H Q \<and> \<not> col A B C \<and> \<not> col A B D` by blast
				have "col Q C G" using collinearorder[OF `axioms` `col C G Q`] by blast
				have "C \<noteq> Q" using betweennotequal[OF `axioms` `bet C G Q`] by blast
				have "Q \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> Q`] .
				have "col C G D" using collinear4[OF `axioms` `col Q C G` `col Q C D` `Q \<noteq> C`] .
				have "col D Q H" using collinearorder[OF `axioms` `col D H Q`] by blast
				have "col D Q C" using collinearorder[OF `axioms` `col C Q D`] by blast
				have "\<not> (col C A B)"
				proof (rule ccontr)
					assume "\<not> (\<not> (col C A B))"
hence "col C A B" by blast
					have "col A B C" using collinearorder[OF `axioms` `col C A B`] by blast
					show "False" using `col A B C` `col A B G \<and> col A B H \<and> bet C G Q \<and> bet D H Q \<and> \<not> col A B C \<and> \<not> col A B D` by blast
				qed
				hence "\<not> col C A B" by blast
				have "\<not> col C A B \<or> \<not> col D A B" using `\<not> col C A B` by blast
				have "\<not> (col C A B \<and> col D A B)"
				proof (rule ccontr)
					assume "\<not> (\<not> (col C A B \<and> col D A B))"
hence "col C A B \<and> col D A B" by blast
					have "\<not> col C A B \<or> \<not> col D A B" using `\<not> col C A B \<or> \<not> col D A B` .
					show "False" using `\<not> col C A B \<or> \<not> col D A B` `col C A B \<and> col D A B` by blast
				qed
				hence "\<not> (col C A B \<and> col D A B)" by blast
				have "col G A B" using collinearorder[OF `axioms` `col A B G`] by blast
				have "col H A B" using collinearorder[OF `axioms` `col A B H`] by blast
				have "col G C D" using collinearorder[OF `axioms` `col C G D`] by blast
				have "col Q D H" using collinearorder[OF `axioms` `col D H Q`] by blast
				have "col Q D C" using collinearorder[OF `axioms` `col C Q D`] by blast
				have "D \<noteq> Q" using betweennotequal[OF `axioms` `bet D H Q`] by blast
				have "Q \<noteq> D" using inequalitysymmetric[OF `axioms` `D \<noteq> Q`] .
				have "col D C H" using collinear4[OF `axioms` `col Q D C` `col Q D H` `Q \<noteq> D`] .
				have "col H C D" using collinearorder[OF `axioms` `col D C H`] by blast
				have "\<not> (C = D)"
				proof (rule ccontr)
					assume "\<not> (C \<noteq> D)"
					hence "C = D" by blast
					have "oppo_side D A B E" using `oppo_side D A B E` .
					have "oppo_side C A B E" using `oppo_side D A B E` `C = D` by blast
					show "False" using `oppo_side C A B E` `\<not> (oppo_side C A B E)` by blast
				qed
				hence "C \<noteq> D" by blast
				have "A \<noteq> B" using `A \<noteq> B` .
				have "G = H" using twolines2[OF `axioms` `C \<noteq> D` `A \<noteq> B` `col G C D` `col G A B` `col H C D` `col H A B` `\<not> (col C A B \<and> col D A B)`] .
				show "False" using `G = H` `G \<noteq> H` by blast
			qed
			hence "G = H" by blast
			have "bet Q G C" using betweennesssymmetryE[OF `axioms` `bet C G Q`] .
			have "bet Q H D" using betweennesssymmetryE[OF `axioms` `bet D H Q`] .
			have "bet Q G D" using `bet Q H D` `G = H` by blast
			have "\<not> (\<not> col E D G)"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> col E D G))"
hence "\<not> col E D G" by blast
				have "\<not> (\<not> col E C G)"
				proof (rule ccontr)
					assume "\<not> (\<not> (\<not> col E C G))"
hence "\<not> col E C G" by blast
					have "\<not> (bet G C D)"
					proof (rule ccontr)
						assume "\<not> (\<not> (bet G C D))"
hence "bet G C D" by blast
						have "oppo_side D A B E" using `oppo_side D A B E` .
						have "oppo_side C A B E" using n9_5b[OF `axioms` `oppo_side D A B E` `bet G C D` `\<not> col E D G` `col A B G`] .
						show "False" using `oppo_side C A B E` `\<not> (oppo_side C A B E)` by blast
					qed
					hence "\<not> (bet G C D)" by blast
					have "\<not> (bet G D C)"
					proof (rule ccontr)
						assume "\<not> (\<not> (bet G D C))"
hence "bet G D C" by blast
						have "\<not> (col G C E)"
						proof (rule ccontr)
							assume "\<not> (\<not> (col G C E))"
hence "col G C E" by blast
							have "col E C G" using collinearorder[OF `axioms` `col G C E`] by blast
							show "False" using `col E C G` `\<not> col E C G` by blast
						qed
						hence "\<not> col G C E" by blast
						have "oppo_side C A B E" using n9_5a[OF `axioms` `oppo_side D A B E` `bet G D C` `\<not> col G C E` `col A B G`] .
						show "False" using `oppo_side C A B E` `\<not> (oppo_side C A B E)` by blast
					qed
					hence "\<not> (bet G D C)" by blast
					have "C = D" using outerconnectivity[OF `axioms` `bet Q G C` `bet Q G D` `\<not> (bet G C D)` `\<not> (bet G D C)`] .
					have "oppo_side C A B E" using `oppo_side D A B E` `C = D` by blast
					show "False" using `oppo_side C A B E` `\<not> (oppo_side C A B E)` by blast
				qed
				hence "col E C G" by blast
				have "col Q G D" using collinear_b `axioms` `bet Q G D` by blast
				have "col Q G C" using collinear_b `axioms` `bet Q G C` by blast
				have "Q \<noteq> G" using betweennotequal[OF `axioms` `bet Q G C`] by blast
				have "col G D C" using collinear4[OF `axioms` `col Q G D` `col Q G C` `Q \<noteq> G`] .
				have "col C G D" using collinearorder[OF `axioms` `col G D C`] by blast
				have "col C G E" using collinearorder[OF `axioms` `col E C G`] by blast
				have "G \<noteq> C" using betweennotequal[OF `axioms` `bet Q G C`] by blast
				have "C \<noteq> G" using inequalitysymmetric[OF `axioms` `G \<noteq> C`] .
				have "col G D E" using collinear4[OF `axioms` `col C G D` `col C G E` `C \<noteq> G`] .
				have "col E D G" using collinearorder[OF `axioms` `col G D E`] by blast
				show "False" using `col E D G` `\<not> col E D G` by blast
			qed
			hence "col E D G" by blast
			have "col A B W" using `bet D W E \<and> col A B W \<and> \<not> col A B D` by blast
			have "col A B G" using `col A B G` .
			have "col D W E" using collinear_b `axioms` `bet D W E \<and> col A B W \<and> \<not> col A B D` by blast
			have "col D E W" using collinearorder[OF `axioms` `col D W E`] by blast
			have "col D E G" using collinearorder[OF `axioms` `col E D G`] by blast
			have "D \<noteq> E" using betweennotequal[OF `axioms` `bet D W E`] by blast
			have "col E W G" using collinear4[OF `axioms` `col D E W` `col D E G` `D \<noteq> E`] .
			have "col E W D" using collinearorder[OF `axioms` `col D E W`] by blast
			have "W \<noteq> E" using betweennotequal[OF `axioms` `bet D W E`] by blast
			have "E \<noteq> W" using inequalitysymmetric[OF `axioms` `W \<noteq> E`] .
			have "col W G D" using collinear4[OF `axioms` `col E W G` `col E W D` `E \<noteq> W`] .
			have "col B W G" using collinear4[OF `axioms` `col A B W` `col A B G` `A \<noteq> B`] .
			have "col W G B" using collinearorder[OF `axioms` `col B W G`] by blast
			have "col B A W" using collinearorder[OF `axioms` `col A B W`] by blast
			have "col B A G" using collinearorder[OF `axioms` `col A B G`] by blast
			have "col A W G" using collinear4[OF `axioms` `col B A W` `col B A G` `B \<noteq> A`] .
			have "col W G A" using collinearorder[OF `axioms` `col A W G`] by blast
			have "\<not> (W \<noteq> G)"
			proof (rule ccontr)
				assume "\<not> (\<not> (W \<noteq> G))"
hence "W \<noteq> G" by blast
				have "col G D B" using collinear4[OF `axioms` `col W G D` `col W G B` `W \<noteq> G`] .
				have "col G B D" using collinearorder[OF `axioms` `col G D B`] by blast
				have "col G B A" using collinearorder[OF `axioms` `col A B G`] by blast
				have "\<not> (G \<noteq> B)"
				proof (rule ccontr)
					assume "\<not> (\<not> (G \<noteq> B))"
hence "G \<noteq> B" by blast
					have "col B D A" using collinear4[OF `axioms` `col G B D` `col G B A` `G \<noteq> B`] .
					have "col A B D" using collinearorder[OF `axioms` `col B D A`] by blast
					have "\<not> col A B D" using `bet D W E \<and> col A B W \<and> \<not> col A B D` by blast
					show "False" using `\<not> col A B D` `col A B D` by blast
				qed
				hence "G = B" by blast
				have "col G D A" using collinear4[OF `axioms` `col W G D` `col W G A` `W \<noteq> G`] .
				have "col G A D" using collinearorder[OF `axioms` `col G D A`] by blast
				have "col G A B" using collinearorder[OF `axioms` `col A B G`] by blast
				have "\<not> (G \<noteq> A)"
				proof (rule ccontr)
					assume "\<not> (\<not> (G \<noteq> A))"
hence "G \<noteq> A" by blast
					have "col A D B" using collinear4[OF `axioms` `col G A D` `col G A B` `G \<noteq> A`] .
					have "col A B D" using collinearorder[OF `axioms` `col A D B`] by blast
					have "\<not> col A B D" using `bet D W E \<and> col A B W \<and> \<not> col A B D` by blast
					show "False" using `\<not> col A B D` `col A B D` by blast
				qed
				hence "G = A" by blast
				have "A = G" using equalitysymmetric[OF `axioms` `G = A`] .
				have "B = G" using equalitysymmetric[OF `axioms` `G = B`] .
				have "A = B" using equalitytransitiveE[OF `axioms` `A = G` `B = G`] .
				have "A \<noteq> B" using `A \<noteq> B` .
				show "False" using `A \<noteq> B` `A = B` by blast
			qed
			hence "W = G" by blast
			have "bet D W E" using `bet D W E` .
			have "bet D G E" using `bet D W E` `W = G` by blast
			have "bet E G D" using betweennesssymmetryE[OF `axioms` `bet D G E`] .
			have "\<not> (bet G D C)"
			proof (rule ccontr)
				assume "\<not> (\<not> (bet G D C))"
hence "bet G D C" by blast
				have "bet E G C" using n3_7b[OF `axioms` `bet E G D` `bet G D C`] .
				have "bet C G E" using betweennesssymmetryE[OF `axioms` `bet E G C`] .
				have "oppo_side C A B E" using oppositeside_b[OF `axioms` `bet C G E` `col A B G` `\<not> col A B C`] .
				show "False" using `oppo_side C A B E` `\<not> (oppo_side C A B E)` by blast
			qed
			hence "\<not> (bet G D C)" by blast
			have "\<not> (bet G C D)"
			proof (rule ccontr)
				assume "\<not> (\<not> (bet G C D))"
hence "bet G C D" by blast
				have "bet E G C" using innertransitivityE[OF `axioms` `bet E G D` `bet G C D`] .
				have "bet C G E" using betweennesssymmetryE[OF `axioms` `bet E G C`] .
				have "oppo_side C A B E" using oppositeside_b[OF `axioms` `bet C G E` `col A B G` `\<not> col A B C`] .
				show "False" using `oppo_side C A B E` `\<not> (oppo_side C A B E)` by blast
			qed
			hence "\<not> (bet G C D)" by blast
			have "\<not> (bet C G D)"
			proof (rule ccontr)
				assume "\<not> (\<not> (bet C G D))"
hence "bet C G D" by blast
				have "bet D G Q" using `bet D H Q` `G = H` by blast
				have "bet C G Q" using `bet C G Q` .
				have "bet D G C" using betweennesssymmetryE[OF `axioms` `bet C G D`] .
				have "\<not> (bet G D C)"
				proof (rule ccontr)
					assume "\<not> (\<not> (bet G D C))"
hence "bet G D C" by blast
					have "bet C D G" using betweennesssymmetryE[OF `axioms` `bet G D C`] .
					have "bet D G C" using `bet D G C` .
					have "bet C G C" using n3_7a[OF `axioms` `bet C D G` `bet D G C`] .
					have "C \<noteq> C" using betweennotequal[OF `axioms` `bet C G C`] by blast
					have "C = C" using equalityreflexiveE[OF `axioms`] .
					show "False" using `C = C` `C \<noteq> C` by blast
				qed
				hence "\<not> (bet G D C)" by blast
				have "\<not> (bet G C D)"
				proof (rule ccontr)
					assume "\<not> (\<not> (bet G C D))"
hence "bet G C D" by blast
					have "bet C G C" using innertransitivityE[OF `axioms` `bet C G D` `bet G C D`] .
					have "C \<noteq> C" using betweennotequal[OF `axioms` `bet C G C`] by blast
					have "C = C" using equalityreflexiveE[OF `axioms`] .
					show "False" using `C = C` `C \<noteq> C` by blast
				qed
				hence "\<not> (bet G C D)" by blast
				have "bet Q G D" using betweennesssymmetryE[OF `axioms` `bet D G Q`] .
				have "bet Q G C" using betweennesssymmetryE[OF `axioms` `bet C G Q`] .
				have "C = D" using outerconnectivity[OF `axioms` `bet Q G C` `bet Q G D` `\<not> (bet G C D)` `\<not> (bet G D C)`] .
				have "oppo_side C A B E" using `oppo_side D A B E` `C = D` by blast
				show "False" using `oppo_side C A B E` `\<not> (oppo_side C A B E)` by blast
			qed
			hence "\<not> (bet C G D)" by blast
			have "col Q C D" using collinearorder[OF `axioms` `col C Q D`] by blast
			have "col Q G C" using collinear_b `axioms` `bet Q G C` by blast
			have "col Q C G" using collinearorder[OF `axioms` `col Q G C`] by blast
			have "Q \<noteq> C" using betweennotequal[OF `axioms` `bet Q G C`] by blast
			have "col C D G" using collinear4[OF `axioms` `col Q C D` `col Q C G` `Q \<noteq> C`] .
			have "col G C D" using collinearorder[OF `axioms` `col C D G`] by blast
			have "G = C \<or> G = D \<or> C = D \<or> bet C G D \<or> bet G C D \<or> bet G D C" using collinear_f[OF `axioms` `col G C D`] .
			consider "G = C"|"G = D"|"C = D"|"bet C G D"|"bet G C D"|"bet G D C" using `G = C \<or> G = D \<or> C = D \<or> bet C G D \<or> bet G C D \<or> bet G D C`  by blast
			hence "oppo_side C A B E"
			proof (cases)
				assume "G = C"
				have "\<not> (\<not> (oppo_side C A B E))"
				proof (rule ccontr)
					assume "\<not> (\<not> (\<not> (oppo_side C A B E)))"
hence "\<not> (oppo_side C A B E)" by blast
					have "col A B G" using `col A B G` .
					have "col A B C" using `col A B G` `G = C` by blast
					have "\<not> col A B C" using `\<not> col A B C` .
					show "False" using `\<not> col A B C` `col A B C` by blast
				qed
				hence "oppo_side C A B E" by blast
				thus ?thesis by blast
			next
				assume "G = D"
				have "\<not> (\<not> (oppo_side C A B E))"
				proof (rule ccontr)
					assume "\<not> (\<not> (\<not> (oppo_side C A B E)))"
hence "\<not> (oppo_side C A B E)" by blast
					have "col A B G" using `col A B G` .
					have "col A B D" using `col A B G` `G = D` by blast
					have "\<not> col A B D" using `bet D W E \<and> col A B W \<and> \<not> col A B D` by blast
					show "False" using `\<not> col A B D` `col A B D` by blast
				qed
				hence "oppo_side C A B E" by blast
				thus ?thesis by blast
			next
				assume "C = D"
				have "\<not> (\<not> (oppo_side C A B E))"
				proof (rule ccontr)
					assume "\<not> (\<not> (\<not> (oppo_side C A B E)))"
hence "\<not> (oppo_side C A B E)" by blast
					have "oppo_side D A B E" using `oppo_side D A B E` .
					have "oppo_side C A B E" using `oppo_side D A B E` `C = D` by blast
					show "False" using `oppo_side C A B E` `\<not> (oppo_side C A B E)` by blast
				qed
				hence "oppo_side C A B E" by blast
				thus ?thesis by blast
			next
				assume "bet C G D"
				have "\<not> (\<not> (oppo_side C A B E))"
				proof (rule ccontr)
					assume "\<not> (\<not> (\<not> (oppo_side C A B E)))"
hence "\<not> (oppo_side C A B E)" by blast
					have "\<not> (bet C G D)" using `\<not> (bet C G D)` .
					show "False" using `\<not> (bet C G D)` `bet C G D` by blast
				qed
				hence "oppo_side C A B E" by blast
				thus ?thesis by blast
			next
				assume "bet G C D"
				have "\<not> (\<not> (oppo_side C A B E))"
				proof (rule ccontr)
					assume "\<not> (\<not> (\<not> (oppo_side C A B E)))"
hence "\<not> (oppo_side C A B E)" by blast
					have "\<not> (bet G C D)" using `\<not> (bet G C D)` .
					show "False" using `\<not> (bet G C D)` `bet G C D` by blast
				qed
				hence "oppo_side C A B E" by blast
				thus ?thesis by blast
			next
				assume "bet G D C"
				have "\<not> (\<not> (oppo_side C A B E))"
				proof (rule ccontr)
					assume "\<not> (\<not> (\<not> (oppo_side C A B E)))"
hence "\<not> (oppo_side C A B E)" by blast
					have "\<not> (bet G D C)" using `\<not> (bet G D C)` .
					show "False" using `\<not> (bet G D C)` `bet G D C` by blast
				qed
				hence "oppo_side C A B E" by blast
				thus ?thesis by blast
			qed
			show "False" using `oppo_side C A B E` `\<not> (oppo_side C A B E)` by blast
		qed
		hence "oppo_side C A B E" by blast
		thus ?thesis by blast
	next
		assume "\<not> col C Q D"
		have "\<not> (\<not> (oppo_side C A B E))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (oppo_side C A B E)))"
hence "\<not> (oppo_side C A B E)" by blast
			have "\<not> (col Q C D)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col Q C D))"
hence "col Q C D" by blast
				have "col C Q D" using collinearorder[OF `axioms` `col Q C D`] by blast
				show "False" using `col C Q D` `\<not> col C Q D` by blast
			qed
			hence "\<not> col Q C D" by blast
			obtain F where "bet C F H \<and> bet D F G" using Pasch_innerE[OF `axioms` `bet C G Q` `bet D H Q` `\<not> col C Q D`]  by  blast
			have "bet C F H" using `bet C F H \<and> bet D F G` by blast
			have "bet D F G" using `bet C F H \<and> bet D F G` by blast
			have "bet H F C" using betweennesssymmetryE[OF `axioms` `bet C F H`] .
			have "bet G F D" using betweennesssymmetryE[OF `axioms` `bet D F G`] .
			have "\<not> (col E D G)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col E D G))"
hence "col E D G" by blast
				have "\<not> (W \<noteq> G)"
				proof (rule ccontr)
					assume "\<not> (\<not> (W \<noteq> G))"
hence "W \<noteq> G" by blast
					have "col D E G" using collinearorder[OF `axioms` `col E D G`] by blast
					have "col D W E" using collinear_b `axioms` `bet D W E \<and> col A B W \<and> \<not> col A B D` by blast
					have "col E D G" using collinearorder[OF `axioms` `col D E G`] by blast
					have "col E D W" using collinearorder[OF `axioms` `col D W E`] by blast
					have "D \<noteq> E" using betweennotequal[OF `axioms` `bet D W E`] by blast
					have "E \<noteq> D" using inequalitysymmetric[OF `axioms` `D \<noteq> E`] .
					have "col D G W" using collinear4[OF `axioms` `col E D G` `col E D W` `E \<noteq> D`] .
					have "col G W D" using collinearorder[OF `axioms` `col D G W`] by blast
					have "col A B W" using `bet D W E \<and> col A B W \<and> \<not> col A B D` by blast
					have "col A B G" using `col A B G` .
					have "B = B" using equalityreflexiveE[OF `axioms`] .
					have "col A B B" using collinear_b `axioms` `B = B` by blast
					have "G \<noteq> W" using inequalitysymmetric[OF `axioms` `W \<noteq> G`] .
					have "col G W B" using collinear5[OF `axioms` `A \<noteq> B` `col A B G` `col A B W` `col A B B`] .
					have "col W D B" using collinear4[OF `axioms` `col G W D` `col G W B` `G \<noteq> W`] .
					have "col B A W" using collinearorder[OF `axioms` `col A B W`] by blast
					have "col B A G" using collinearorder[OF `axioms` `col A B G`] by blast
					have "A = A" using equalityreflexiveE[OF `axioms`] .
					have "col B A A" using collinear_b `axioms` `A = A` by blast
					have "G \<noteq> W" using `G \<noteq> W` .
					have "col G W A" using collinear5[OF `axioms` `B \<noteq> A` `col B A G` `col B A W` `col B A A`] .
					have "col W D A" using collinear4[OF `axioms` `col G W D` `col G W A` `G \<noteq> W`] .
					have "D \<noteq> W" using betweennotequal[OF `axioms` `bet D W E`] by blast
					have "W \<noteq> D" using inequalitysymmetric[OF `axioms` `D \<noteq> W`] .
					have "col D B A" using collinear4[OF `axioms` `col W D B` `col W D A` `W \<noteq> D`] .
					have "col A B D" using collinearorder[OF `axioms` `col D B A`] by blast
					have "\<not> col A B D" using `bet D W E \<and> col A B W \<and> \<not> col A B D` by blast
					show "False" using `\<not> col A B D` `col A B D` by blast
				qed
				hence "W = G" by blast
				have "bet D W E" using `bet D W E` .
				have "bet D G E" using `bet D W E` `W = G` by blast
				have "bet E G D" using betweennesssymmetryE[OF `axioms` `bet D G E`] .
				have "bet G F D" using betweennesssymmetryE[OF `axioms` `bet D F G`] .
				have "bet E G F" using innertransitivityE[OF `axioms` `bet E G D` `bet G F D`] .
				have "bet H F C" using `bet H F C` .
				have "\<not> (col H C E)"
				proof (rule ccontr)
					assume "\<not> (\<not> (col H C E))"
hence "col H C E" by blast
					have "col H E C" using collinearorder[OF `axioms` `col H C E`] by blast
					have "col E H C" using collinearorder[OF `axioms` `col H C E`] by blast
					have "col C F H" using collinear_b `axioms` `bet C F H \<and> bet D F G` by blast
					have "col H C F" using collinearorder[OF `axioms` `col C F H`] by blast
					have "col H C E" using collinearorder[OF `axioms` `col E H C`] by blast
					have "C \<noteq> H" using betweennotequal[OF `axioms` `bet C F H`] by blast
					have "H \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> H`] .
					have "col C F E" using collinear4[OF `axioms` `col H C F` `col H C E` `H \<noteq> C`] .
					have "col E F C" using collinearorder[OF `axioms` `col C F E`] by blast
					have "bet D F G" using `bet D F G` .
					have "bet D G E" using `bet D G E` .
					have "bet D F E" using n3_6b[OF `axioms` `bet D F G` `bet D G E`] .
					have "col D F E" using collinear_b `axioms` `bet D F E` by blast
					have "col E F D" using collinearorder[OF `axioms` `col D F E`] by blast
					have "F \<noteq> E" using betweennotequal[OF `axioms` `bet D F E`] by blast
					have "E \<noteq> F" using inequalitysymmetric[OF `axioms` `F \<noteq> E`] .
					have "col F C D" using collinear4[OF `axioms` `col E F C` `col E F D` `E \<noteq> F`] .
					have "col F D C" using collinearorder[OF `axioms` `col F C D`] by blast
					have "col D F G" using collinear_b `axioms` `bet C F H \<and> bet D F G` by blast
					have "col F D G" using collinearorder[OF `axioms` `col D F G`] by blast
					have "D \<noteq> F" using betweennotequal[OF `axioms` `bet D F E`] by blast
					have "F \<noteq> D" using inequalitysymmetric[OF `axioms` `D \<noteq> F`] .
					have "col D C G" using collinear4[OF `axioms` `col F D C` `col F D G` `F \<noteq> D`] .
					have "col G C D" using collinearorder[OF `axioms` `col D C G`] by blast
					have "col C G Q" using collinear_b `axioms` `col A B G \<and> col A B H \<and> bet C G Q \<and> bet D H Q \<and> \<not> col A B C \<and> \<not> col A B D` by blast
					have "col G C Q" using collinearorder[OF `axioms` `col C G Q`] by blast
					have "C \<noteq> G" using betweennotequal[OF `axioms` `bet C G Q`] by blast
					have "G \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> G`] .
					have "col C D Q" using collinear4[OF `axioms` `col G C D` `col G C Q` `G \<noteq> C`] .
					have "col Q C D" using collinearorder[OF `axioms` `col C D Q`] by blast
					have "\<not> col Q C D" using `\<not> col Q C D` .
					show "False" using `\<not> col Q C D` `col Q C D` by blast
				qed
				hence "\<not> col H C E" by blast
				obtain M where "bet E M C \<and> bet H G M" using Pasch_outerE[OF `axioms` `bet E G F` `bet H F C` `\<not> col H C E`]  by  blast
				have "bet E M C" using `bet E M C \<and> bet H G M` by blast
				have "bet H G M" using `bet E M C \<and> bet H G M` by blast
				have "col H G M" using collinear_b `axioms` `bet E M C \<and> bet H G M` by blast
				have "col A B H" using `col A B H` .
				have "col A B G" using `col A B G` .
				have "col B H G" using collinear4[OF `axioms` `col A B H` `col A B G` `A \<noteq> B`] .
				have "col H G B" using collinearorder[OF `axioms` `col B H G`] by blast
				have "H \<noteq> G" using betweennotequal[OF `axioms` `bet H G M`] by blast
				have "col G M B" using collinear4[OF `axioms` `col H G M` `col H G B` `H \<noteq> G`] .
				have "col G B M" using collinearorder[OF `axioms` `col G M B`] by blast
				have "col G B A" using collinearorder[OF `axioms` `col A B G`] by blast
				consider "B = G"|"B \<noteq> G" by blast
				hence "col A B M"
				proof (cases)
					assume "B = G"
					have "col B A H" using collinearorder[OF `axioms` `col A B H`] by blast
					have "col B A G" using collinearorder[OF `axioms` `col A B G`] by blast
					have "col A H G" using collinear4[OF `axioms` `col B A H` `col B A G` `B \<noteq> A`] .
					have "col H G A" using collinearorder[OF `axioms` `col A H G`] by blast
					have "col H G M" using `col H G M` .
					have "col G A M" using collinear4[OF `axioms` `col H G A` `col H G M` `H \<noteq> G`] .
					have "col B A M" using `col G A M` `B = G` by blast
					have "col A B M" using collinearorder[OF `axioms` `col B A M`] by blast
					thus ?thesis by blast
				next
					assume "B \<noteq> G"
					have "G \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> G`] .
					have "col B M A" using collinear4[OF `axioms` `col G B M` `col G B A` `G \<noteq> B`] .
					have "col A B M" using collinearorder[OF `axioms` `col B M A`] by blast
					thus ?thesis by blast
				qed
				have "bet C M E" using betweennesssymmetryE[OF `axioms` `bet E M C`] .
				have "bet C M E \<and> col A B M \<and> \<not> col A B C" using `bet C M E` `col A B M` `col A B G \<and> col A B H \<and> bet C G Q \<and> bet D H Q \<and> \<not> col A B C \<and> \<not> col A B D` by blast
				have "oppo_side C A B E" using oppositeside_b[OF `axioms` `bet C M E` `col A B M` `\<not> col A B C`] .
				have "\<not> (oppo_side C A B E)" using `\<not> (oppo_side C A B E)` .
				show "False" using `\<not> (oppo_side C A B E)` `oppo_side C A B E` by blast
			qed
			hence "\<not> col E D G" by blast
			have "oppo_side F A B E" using n9_5b[OF `axioms` `oppo_side D A B E` `bet G F D` `\<not> col E D G` `col A B G`] .
			have "\<not> (G = H)"
			proof (rule ccontr)
				assume "\<not> (G \<noteq> H)"
				hence "G = H" by blast
				have "col D H Q" using collinear_b `axioms` `col A B G \<and> col A B H \<and> bet C G Q \<and> bet D H Q \<and> \<not> col A B C \<and> \<not> col A B D` by blast
				have "col C G Q" using collinear_b `axioms` `col A B G \<and> col A B H \<and> bet C G Q \<and> bet D H Q \<and> \<not> col A B C \<and> \<not> col A B D` by blast
				have "col Q H D" using collinearorder[OF `axioms` `col D H Q`] by blast
				have "col Q G C" using collinearorder[OF `axioms` `col C G Q`] by blast
				have "col Q H C" using `col Q G C` `G = H` by blast
				have "H \<noteq> Q" using betweennotequal[OF `axioms` `bet D H Q`] by blast
				have "Q \<noteq> H" using inequalitysymmetric[OF `axioms` `H \<noteq> Q`] .
				have "col H D C" using collinear4[OF `axioms` `col Q H D` `col Q H C` `Q \<noteq> H`] .
				have "col H D Q" using collinearorder[OF `axioms` `col D H Q`] by blast
				have "D \<noteq> H" using betweennotequal[OF `axioms` `bet D H Q`] by blast
				have "H \<noteq> D" using inequalitysymmetric[OF `axioms` `D \<noteq> H`] .
				have "col D C Q" using collinear4[OF `axioms` `col H D C` `col H D Q` `H \<noteq> D`] .
				have "col C Q D" using collinearorder[OF `axioms` `col D C Q`] by blast
				have "\<not> col C Q D" using `\<not> col C Q D` .
				show "False" using `\<not> col C Q D` `col C Q D` by blast
			qed
			hence "G \<noteq> H" by blast
			have "\<not> (col H C E)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col H C E))"
hence "col H C E" by blast
				have "bet E W D" using betweennesssymmetryE[OF `axioms` `bet D W E`] .
				have "bet G F D" using betweennesssymmetryE[OF `axioms` `bet D F G`] .
				obtain J where "bet E J F \<and> bet G J W" using Pasch_innerE[OF `axioms` `bet E W D` `bet G F D` `\<not> col E D G`]  by  blast
				have "bet E J F" using `bet E J F \<and> bet G J W` by blast
				have "bet G J W" using `bet E J F \<and> bet G J W` by blast
				have "col G J W" using collinear_b `axioms` `bet E J F \<and> bet G J W` by blast
				have "col E F J" using collinear_b `axioms` `bet E J F \<and> bet G J W` by blast
				have "col F E J" using collinearorder[OF `axioms` `col E F J`] by blast
				have "col C F H" using collinear_b `axioms` `bet C F H \<and> bet D F G` by blast
				have "col C H F" using collinearorder[OF `axioms` `col C F H`] by blast
				have "col C H E" using collinearorder[OF `axioms` `col H C E`] by blast
				have "C \<noteq> H" using betweennotequal[OF `axioms` `bet C F H`] by blast
				have "col H F E" using collinear4[OF `axioms` `col C H F` `col C H E` `C \<noteq> H`] .
				have "col F E H" using collinearorder[OF `axioms` `col H F E`] by blast
				have "bet E J F" using `bet E J F` .
				have "E \<noteq> F" using betweennotequal[OF `axioms` `bet E J F`] by blast
				have "F \<noteq> E" using inequalitysymmetric[OF `axioms` `E \<noteq> F`] .
				have "col F E J" using `col F E J` .
				have "col F E H" using `col F E H` .
				have "col G W J" using collinearorder[OF `axioms` `col G J W`] by blast
				have "col A B G" using `col A B G` .
				have "col A B H" using `col A B H` .
				have "col A B W" using `bet D W E \<and> col A B W \<and> \<not> col A B D` by blast
				have "col G H W" using collinear5[OF `axioms` `A \<noteq> B` `col A B G` `col A B H` `col A B W`] .
				have "col G W H" using collinearorder[OF `axioms` `col G H W`] by blast
				have "\<not> (G = W)"
				proof (rule ccontr)
					assume "\<not> (G \<noteq> W)"
					hence "G = W" by blast
					have "col D W E" using collinear_b `axioms` `bet D W E \<and> col A B W \<and> \<not> col A B D` by blast
					have "col D G E" using `col D W E` `G = W` by blast
					have "col E D G" using collinearorder[OF `axioms` `col D G E`] by blast
					have "\<not> col E D G" using `\<not> col E D G` .
					show "False" using `\<not> col E D G` `col E D G` by blast
				qed
				hence "G \<noteq> W" by blast
				have "col E J H" using collinear4[OF `axioms` `col F E J` `col F E H` `F \<noteq> E`] .
				have "col W J H" using collinear4[OF `axioms` `col G W J` `col G W H` `G \<noteq> W`] .
				have "col J H E" using collinearorder[OF `axioms` `col E J H`] by blast
				have "col J H W" using collinearorder[OF `axioms` `col W J H`] by blast
				have "\<not> (H = W)"
				proof (rule ccontr)
					assume "\<not> (H \<noteq> W)"
					hence "H = W" by blast
					have "col D W E" using collinear_b `axioms` `bet D W E \<and> col A B W \<and> \<not> col A B D` by blast
					have "col D H E" using `col D W E` `H = W` by blast
					have "col D H Q" using collinear_b `axioms` `col A B G \<and> col A B H \<and> bet C G Q \<and> bet D H Q \<and> \<not> col A B C \<and> \<not> col A B D` by blast
					have "D \<noteq> H" using betweennotequal[OF `axioms` `bet D H Q`] by blast
					have "col H E Q" using collinear4[OF `axioms` `col D H E` `col D H Q` `D \<noteq> H`] .
					have "col H E C" using collinearorder[OF `axioms` `col C H E`] by blast
					have "W \<noteq> E" using betweennotequal[OF `axioms` `bet D W E`] by blast
					have "H \<noteq> E" using `W \<noteq> E` `H = W` by blast
					have "col E Q C" using collinear4[OF `axioms` `col H E Q` `col H E C` `H \<noteq> E`] .
					have "col E C Q" using collinearorder[OF `axioms` `col E Q C`] by blast
					have "col E C H" using collinearorder[OF `axioms` `col C H E`] by blast
					have "\<not> (E \<noteq> C)"
					proof (rule ccontr)
						assume "\<not> (\<not> (E \<noteq> C))"
hence "E \<noteq> C" by blast
						have "col C Q H" using collinear4[OF `axioms` `col E C Q` `col E C H` `E \<noteq> C`] .
						have "col H Q C" using collinearorder[OF `axioms` `col C Q H`] by blast
						have "col H Q D" using collinearorder[OF `axioms` `col D H Q`] by blast
						have "H \<noteq> Q" using betweennotequal[OF `axioms` `bet D H Q`] by blast
						have "col Q C D" using collinear4[OF `axioms` `col H Q C` `col H Q D` `H \<noteq> Q`] .
						have "\<not> col Q C D" using `\<not> col Q C D` .
						show "False" using `\<not> col Q C D` `col Q C D` by blast
					qed
					hence "E = C" by blast
					have "col E W D" using collinearorder[OF `axioms` `col D W E`] by blast
					have "col C W D" using `col E W D` `E = C` by blast
					have "col C H D" using `col C W D` `H = W` by blast
					have "col D H C" using collinearorder[OF `axioms` `col C H D`] by blast
					have "col D H Q" using collinear_b `axioms` `col A B G \<and> col A B H \<and> bet C G Q \<and> bet D H Q \<and> \<not> col A B C \<and> \<not> col A B D` by blast
					have "D \<noteq> H" using betweennotequal[OF `axioms` `bet D H Q`] by blast
					have "col H C Q" using collinear4[OF `axioms` `col D H C` `col D H Q` `D \<noteq> H`] .
					have "col H Q C" using collinearorder[OF `axioms` `col H C Q`] by blast
					have "col H Q D" using collinearorder[OF `axioms` `col D H Q`] by blast
					have "H \<noteq> Q" using betweennotequal[OF `axioms` `bet D H Q`] by blast
					have "col Q C D" using collinear4[OF `axioms` `col H Q C` `col H Q D` `H \<noteq> Q`] .
					have "col C Q D" using collinearorder[OF `axioms` `col Q C D`] by blast
					have "\<not> col C Q D" using `\<not> col C Q D` .
					show "False" using `\<not> col C Q D` `col C Q D` by blast
				qed
				hence "H \<noteq> W" by blast
				have "\<not> (J \<noteq> H)"
				proof (rule ccontr)
					assume "\<not> (\<not> (J \<noteq> H))"
hence "J \<noteq> H" by blast
					have "col H E W" using collinear4[OF `axioms` `col J H E` `col J H W` `J \<noteq> H`] .
					have "col H W E" using collinearorder[OF `axioms` `col H E W`] by blast
					have "col H W G" using collinearorder[OF `axioms` `col G H W`] by blast
					have "col W E G" using collinear4[OF `axioms` `col H W E` `col H W G` `H \<noteq> W`] .
					have "col D W E" using collinear_b `axioms` `bet D W E \<and> col A B W \<and> \<not> col A B D` by blast
					have "col W E D" using collinearorder[OF `axioms` `col D W E`] by blast
					have "W \<noteq> E" using betweennotequal[OF `axioms` `bet D W E`] by blast
					have "col E G D" using collinear4[OF `axioms` `col W E G` `col W E D` `W \<noteq> E`] .
					have "col E D G" using collinearorder[OF `axioms` `col E G D`] by blast
					have "\<not> col E D G" using `\<not> col E D G` .
					show "False" using `\<not> col E D G` `col E D G` by blast
				qed
				hence "J = H" by blast
				have "bet E J F" using `bet E J F` .
				have "bet E H F" using `bet E J F` `J = H` by blast
				have "bet F H E" using betweennesssymmetryE[OF `axioms` `bet E H F`] .
				have "bet C F H" using `bet C F H` .
				have "bet C H E" using n3_7a[OF `axioms` `bet C F H` `bet F H E`] .
				have "col A B H" using `col A B H` .
				have "oppo_side C A B E" using oppositeside_b[OF `axioms` `bet C H E` `col A B H` `\<not> col A B C`] .
				have "\<not> (oppo_side C A B E)" using `\<not> (oppo_side C A B E)` .
				show "False" using `\<not> (oppo_side C A B E)` `oppo_side C A B E` by blast
			qed
			hence "\<not> col H C E" by blast
			have "oppo_side C A B E" using n9_5a[OF `axioms` `oppo_side F A B E` `bet H F C` `\<not> col H C E` `col A B H`] .
			have "\<not> (oppo_side C A B E)" using `\<not> (oppo_side C A B E)` .
			show "False" using `\<not> (oppo_side C A B E)` `oppo_side C A B E` by blast
		qed
		hence "oppo_side C A B E" by blast
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end