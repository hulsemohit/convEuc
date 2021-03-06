theory collinearbetween
	imports Geometry betweennotequal collinear4 collinearorder inequalitysymmetric
begin

theorem(in euclidean_geometry) collinearbetween:
	assumes 
		"col A E B"
		"col C F D"
		"A \<noteq> B"
		"C \<noteq> D"
		"A \<noteq> E"
		"F \<noteq> D"
		"\<not> (meets A B C D)"
		"bet A H D"
		"col E F H"
	shows "bet E H F"
proof -
	have "\<not> (H = E)"
	proof (rule ccontr)
		assume "\<not> (H \<noteq> E)"
		hence "H = E" by blast
		have "col A E B" using `col A E B` .
		have "col A H B" using `col A E B` `H = E` by blast
		have "col H A B" using collinearorder[OF `col A H B`] by blast
		have "col A H D" using collinear_b `bet A H D` by blast
		have "col H A D" using collinearorder[OF `col A H D`] by blast
		have "A \<noteq> H" using betweennotequal[OF `bet A H D`] by blast
		have "H \<noteq> A" using inequalitysymmetric[OF `A \<noteq> H`] .
		have "col A B D" using collinear4[OF `col H A B` `col H A D` `H \<noteq> A`] .
		have "D = D" using equalityreflexiveE.
		have "col C D D" using collinear_b `D = D` by blast
		have "meets A B C D" using meet_b[OF `A \<noteq> B` `C \<noteq> D` `col A B D` `col C D D`] .
		show "False" using `meets A B C D` `\<not> (meets A B C D)` by blast
	qed
	hence "H \<noteq> E" by blast
	have "\<not> (H = F)"
	proof (rule ccontr)
		assume "\<not> (H \<noteq> F)"
		hence "H = F" by blast
		have "col A H D" using collinear_b `bet A H D` by blast
		have "col A F D" using `col A H D` `H = F` by blast
		have "col F D A" using collinearorder[OF `col A F D`] by blast
		have "col F D C" using collinearorder[OF `col C F D`] by blast
		have "col D A C" using collinear4[OF `col F D A` `col F D C` `F \<noteq> D`] .
		have "col C D A" using collinearorder[OF `col D A C`] by blast
		have "A = A" using equalityreflexiveE.
		have "col A B A" using collinear_b `A = A` by blast
		have "meets A B C D" using meet_b[OF `A \<noteq> B` `C \<noteq> D` `col A B A` `col C D A`] .
		show "False" using `meets A B C D` `\<not> (meets A B C D)` by blast
	qed
	hence "H \<noteq> F" by blast
	have "\<not> (bet E F H)"
	proof (rule ccontr)
		assume "\<not> (\<not> (bet E F H))"
hence "bet E F H" by blast
		have "bet D H A" using betweennesssymmetryE[OF `bet A H D`] .
		have "\<not> (col D A E)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col D A E))"
hence "col D A E" by blast
			have "col E A B" using collinearorder[OF `col A E B`] by blast
			have "col E A D" using collinearorder[OF `col D A E`] by blast
			have "E \<noteq> A" using inequalitysymmetric[OF `A \<noteq> E`] .
			have "col A B D" using collinear4[OF `col E A B` `col E A D` `E \<noteq> A`] .
			have "D = D" using equalityreflexiveE.
			have "col C D D" using collinear_b `D = D` by blast
			have "A \<noteq> B \<and> C \<noteq> D \<and> col A B D \<and> col C D D" using `A \<noteq> B` `C \<noteq> D` `col A B D` `col C D D` by blast
			have "meets A B C D" using meet_b[OF `A \<noteq> B` `C \<noteq> D` `col A B D` `col C D D`] .
			show "False" using `meets A B C D` `\<not> (meets A B C D)` by blast
		qed
		hence "\<not> col D A E" by blast
		obtain Q where "bet E Q A \<and> bet D F Q" using Pasch_outerE[OF `bet E F H` `bet D H A` `\<not> col D A E`]  by  blast
		have "bet E Q A" using `bet E Q A \<and> bet D F Q` by blast
		have "bet D F Q" using `bet E Q A \<and> bet D F Q` by blast
		have "col E Q A" using collinear_b `bet E Q A \<and> bet D F Q` by blast
		have "col D F Q" using collinear_b `bet E Q A \<and> bet D F Q` by blast
		have "col E A Q" using collinearorder[OF `col E Q A`] by blast
		have "col E A B" using collinearorder[OF `col A E B`] by blast
		have "E \<noteq> A" using inequalitysymmetric[OF `A \<noteq> E`] .
		have "col A Q B" using collinear4[OF `col E A Q` `col E A B` `E \<noteq> A`] .
		have "col A B Q" using collinearorder[OF `col A Q B`] by blast
		have "col F D Q" using collinearorder[OF `col D F Q`] by blast
		have "col F D C" using collinearorder[OF `col C F D`] by blast
		have "col D Q C" using collinear4[OF `col F D Q` `col F D C` `F \<noteq> D`] .
		have "col C D Q" using collinearorder[OF `col D Q C`] by blast
		have "meets A B C D" using meet_b[OF `A \<noteq> B` `C \<noteq> D` `col A B Q` `col C D Q`] .
		show "False" using `meets A B C D` `\<not> (meets A B C D)` by blast
	qed
	hence "\<not> (bet E F H)" by blast
	have "\<not> (bet F E H)"
	proof (rule ccontr)
		assume "\<not> (\<not> (bet F E H))"
hence "bet F E H" by blast
		have "bet A H D" using `bet A H D` .
		have "\<not> (col A D F)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col A D F))"
hence "col A D F" by blast
			have "col F D C" using collinearorder[OF `col C F D`] by blast
			have "col F D A" using collinearorder[OF `col A D F`] by blast
			have "col D C A" using collinear4[OF `col F D C` `col F D A` `F \<noteq> D`] .
			have "col C D A" using collinearorder[OF `col D C A`] by blast
			have "A = A" using equalityreflexiveE.
			have "col A B A" using collinear_b `A = A` by blast
			have "A \<noteq> B \<and> C \<noteq> D \<and> col A B A \<and> col C D A" using `A \<noteq> B` `C \<noteq> D` `col A B A` `col C D A` by blast
			have "meets A B C D" using meet_b[OF `A \<noteq> B` `C \<noteq> D` `col A B A` `col C D A`] .
			show "False" using `meets A B C D` `\<not> (meets A B C D)` by blast
		qed
		hence "\<not> col A D F" by blast
		obtain R where "bet F R D \<and> bet A E R" using Pasch_outerE[OF `bet F E H` `bet A H D` `\<not> col A D F`]  by  blast
		have "bet F R D" using `bet F R D \<and> bet A E R` by blast
		have "bet A E R" using `bet F R D \<and> bet A E R` by blast
		have "col F R D" using collinear_b `bet F R D \<and> bet A E R` by blast
		have "col A E R" using collinear_b `bet F R D \<and> bet A E R` by blast
		have "col F D R" using collinearorder[OF `col F R D`] by blast
		have "col F D C" using collinearorder[OF `col C F D`] by blast
		have "col D R C" using collinear4[OF `col F D R` `col F D C` `F \<noteq> D`] .
		have "col C D R" using collinearorder[OF `col D R C`] by blast
		have "col E A R" using collinearorder[OF `col A E R`] by blast
		have "col E A B" using collinearorder[OF `col A E B`] by blast
		have "A \<noteq> E" using betweennotequal[OF `bet A E R`] by blast
		have "E \<noteq> A" using inequalitysymmetric[OF `A \<noteq> E`] .
		have "col A R B" using collinear4[OF `col E A R` `col E A B` `E \<noteq> A`] .
		have "col A B R" using collinearorder[OF `col A R B`] by blast
		have "meets A B C D" using meet_b[OF `A \<noteq> B` `C \<noteq> D` `col A B R` `col C D R`] .
		show "False" using `meets A B C D` `\<not> (meets A B C D)` by blast
	qed
	hence "\<not> (bet F E H)" by blast
	have "\<not> (E = F)"
	proof (rule ccontr)
		assume "\<not> (E \<noteq> F)"
		hence "E = F" by blast
		have "col C D F" using collinearorder[OF `col C F D`] by blast
		have "col A B E" using collinearorder[OF `col A E B`] by blast
		have "col A B F" using `col A B E` `E = F` by blast
		have "meets A B C D" using meet_b[OF `A \<noteq> B` `C \<noteq> D` `col A B F` `col C D F`] .
		show "False" using `meets A B C D` `\<not> (meets A B C D)` by blast
	qed
	hence "E \<noteq> F" by blast
	have "col E F H" using `col E F H` .
	have "E = F \<or> E = H \<or> F = H \<or> bet F E H \<or> bet E F H \<or> bet E H F" using collinear_f[OF `col E F H`] .
	consider "E = F"|"E = H"|"F = H"|"bet F E H"|"bet E F H"|"bet E H F" using `E = F \<or> E = H \<or> F = H \<or> bet F E H \<or> bet E F H \<or> bet E H F`  by blast
	hence "bet E H F"
	proof (cases)
		assume "E = F"
		have "\<not> (\<not> (bet E H F))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet E H F)))"
hence "\<not> (bet E H F)" by blast
			have "E \<noteq> F" using `E \<noteq> F` .
			show "False" using `E \<noteq> F` `E = F` by blast
		qed
		hence "bet E H F" by blast
		thus ?thesis by blast
	next
		assume "E = H"
		have "\<not> (\<not> (bet E H F))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet E H F)))"
hence "\<not> (bet E H F)" by blast
			have "E \<noteq> H" using inequalitysymmetric[OF `H \<noteq> E`] .
			show "False" using `E \<noteq> H` `E = H` by blast
		qed
		hence "bet E H F" by blast
		thus ?thesis by blast
	next
		assume "F = H"
		have "\<not> (\<not> (bet E H F))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet E H F)))"
hence "\<not> (bet E H F)" by blast
			have "F \<noteq> H" using inequalitysymmetric[OF `H \<noteq> F`] .
			show "False" using `F \<noteq> H` `F = H` by blast
		qed
		hence "bet E H F" by blast
		thus ?thesis by blast
	next
		assume "bet F E H"
		have "\<not> (\<not> (bet E H F))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet E H F)))"
hence "\<not> (bet E H F)" by blast
			have "\<not> (bet F E H)" using `\<not> (bet F E H)` .
			show "False" using `\<not> (bet F E H)` `bet F E H` by blast
		qed
		hence "bet E H F" by blast
		thus ?thesis by blast
	next
		assume "bet E F H"
		have "\<not> (\<not> (bet E H F))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet E H F)))"
hence "\<not> (bet E H F)" by blast
			have "\<not> (bet E F H)" using `\<not> (bet E F H)` .
			show "False" using `\<not> (bet E F H)` `bet E F H` by blast
		qed
		hence "bet E H F" by blast
		thus ?thesis by blast
	next
		assume "bet E H F"
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end