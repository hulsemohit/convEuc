theory twolines
	imports Geometry betweennotequal collinear1 collinear4 collinearorder
begin

theorem(in euclidean_geometry) twolines:
	assumes 
		"cuts A B C D E"
		"cuts A B C D F"
		"\<not> col B C D"
	shows "E = F"
proof -
	have "bet A E B \<and> bet C E D \<and> \<not> col A B C \<and> \<not> col A B D" using cut_f[OF `cuts A B C D E`] .
	have "bet A E B" using `bet A E B \<and> bet C E D \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "bet A F B \<and> bet C F D \<and> \<not> col A B C \<and> \<not> col A B D" using cut_f[OF `cuts A B C D F`] .
	have "bet A F B" using `bet A F B \<and> bet C F D \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "col A E B" using collinear_b `bet A E B \<and> bet C E D \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "col A B E" using collinearorder[OF `col A E B`] by blast
	have "col A F B" using collinear_b `bet A F B \<and> bet C F D \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "col A B F" using collinearorder[OF `col A F B`] by blast
	have "col A B E" using `col A B E` .
	have "A \<noteq> B" using betweennotequal[OF `bet A E B`] by blast
	have "col B E F" using collinear4[OF `col A B E` `col A B F` `A \<noteq> B`] .
	have "col E F B" using collinearorder[OF `col B E F`] by blast
	have "bet C E D" using `bet A E B \<and> bet C E D \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "col C E D" using collinear_b `bet A E B \<and> bet C E D \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "bet C F D" using `bet A F B \<and> bet C F D \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "col C F D" using collinear_b `bet A F B \<and> bet C F D \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "col C D F" using collinearorder[OF `col C F D`] by blast
	have "col C E D" using `col C E D` .
	have "col C D E" using collinearorder[OF `col C E D`] by blast
	have "col C D F" using `col C D F` .
	have "C \<noteq> D" using betweennotequal[OF `bet C E D`] by blast
	have "col D E F" using collinear4[OF `col C D E` `col C D F` `C \<noteq> D`] .
	have "col E F D" using collinearorder[OF `col D E F`] by blast
	have "col C D E" using `col C D E` .
	have "col D C E" using collinear1[OF `col C D E`] .
	have "col D C F" using collinear1[OF `col C D F`] .
	have "bet D E C" using betweennesssymmetryE[OF `bet C E D`] .
	have "D \<noteq> C" using betweennotequal[OF `bet D E C`] by blast
	have "col C E F" using collinear4[OF `col D C E` `col D C F` `D \<noteq> C`] .
	have "col E F C" using collinearorder[OF `col C E F`] by blast
	have "col E F B" using `col E F B` .
	have "col E F C" using `col E F C` .
	have "col E F D" using `col E F D` .
	have "\<not> (E \<noteq> F)"
	proof (rule ccontr)
		assume "\<not> (\<not> (E \<noteq> F))"
hence "E \<noteq> F" by blast
		have "col F B C" using collinear4[OF `col E F B` `col E F C` `E \<noteq> F`] .
		have "col F B D" using collinear4[OF `col E F B` `col E F D` `E \<noteq> F`] .
		have "\<not> (F = B)"
		proof (rule ccontr)
			assume "\<not> (F \<noteq> B)"
			hence "F = B" by blast
			have "col F C D" using collinear_b `bet A F B \<and> bet C F D \<and> \<not> col A B C \<and> \<not> col A B D` by blast
			have "col B C D" using `col F C D` `F = B` by blast
			have "\<not> col B C D" using `\<not> col B C D` .
			show "False" using `\<not> col B C D` `col B C D` by blast
		qed
		hence "F \<noteq> B" by blast
		have "col B C D" using collinear4[OF `col F B C` `col F B D` `F \<noteq> B`] .
		show "False" using `col B C D` `\<not> col B C D` by blast
	qed
	hence "E = F" by blast
	thus ?thesis by blast
qed

end