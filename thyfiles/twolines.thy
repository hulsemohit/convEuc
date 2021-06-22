theory twolines
	imports Axioms Definitions Theorems
begin

theorem twolines:
	assumes: `axioms`
		"cuts A B C D E"
		"cuts A B C D F"
		"\<not> col B C D"
	shows: "E = F"
proof -
	have "bet A E B \<and> bet C E D \<and> \<not> col A B C \<and> \<not> col A B D" sorry
	have "bet A E B" using `bet A E B \<and> bet C E D \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "bet A F B \<and> bet C F D \<and> \<not> col A B C \<and> \<not> col A B D" sorry
	have "bet A F B" using `bet A F B \<and> bet C F D \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "col A E B" using col_b `axioms` `bet A E B \<and> bet C E D \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "col A B E" using collinearorder[OF `axioms` `col A E B`] by blast
	have "col A F B" using col_b `axioms` `bet A F B \<and> bet C F D \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "col A B F" using collinearorder[OF `axioms` `col A F B`] by blast
	have "col A B E" using `col A B E` .
	have "A \<noteq> B" using betweennotequal[OF `axioms` `bet A E B`] by blast
	have "col B E F" using collinear4[OF `axioms` `col A B E` `col A B F` `A \<noteq> B`] .
	have "col E F B" using collinearorder[OF `axioms` `col B E F`] by blast
	have "bet C E D" using `bet A E B \<and> bet C E D \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "col C E D" using col_b `axioms` `bet A E B \<and> bet C E D \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "bet C F D" using `bet A F B \<and> bet C F D \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "col C F D" using col_b `axioms` `bet A F B \<and> bet C F D \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "col C D F" using collinearorder[OF `axioms` `col C F D`] by blast
	have "col C E D" using `col C E D` .
	have "col C D E" using collinearorder[OF `axioms` `col C E D`] by blast
	have "col C D F" using `col C D F` .
	have "C \<noteq> D" using betweennotequal[OF `axioms` `bet C E D`] by blast
	have "col D E F" using collinear4[OF `axioms` `col C D E` `col C D F` `C \<noteq> D`] .
	have "col E F D" using collinearorder[OF `axioms` `col D E F`] by blast
	have "col C D E" using `col C D E` .
	have "col D C E" using collinear1[OF `axioms` `col C D E`] .
	have "col D C F" using collinear1[OF `axioms` `col C D F`] .
	have "bet D E C" using betweennesssymmetryE[OF `axioms` `bet C E D`] .
	have "D \<noteq> C" using betweennotequal[OF `axioms` `bet D E C`] by blast
	have "col C E F" using collinear4[OF `axioms` `col D C E` `col D C F` `D \<noteq> C`] .
	have "col E F C" using collinearorder[OF `axioms` `col C E F`] by blast
	have "col E F B" using `col E F B` .
	have "col E F C" using `col E F C` .
	have "col E F D" using `col E F D` .
	have "\<not> (E \<noteq> F)"
	proof (rule ccontr)
		assume "E \<noteq> F"
		have "col F B C" using collinear4[OF `axioms` `col E F B` `col E F C` `E \<noteq> F`] .
		have "col F B D" using collinear4[OF `axioms` `col E F B` `col E F D` `E \<noteq> F`] .
		have "\<not> (F = B)"
		proof (rule ccontr)
			assume "F = B"
			have "col F C D" using col_b `axioms` `bet A F B \<and> bet C F D \<and> \<not> col A B C \<and> \<not> col A B D` by blast
			have "col B C D" sorry
			have "\<not> col B C D" using `\<not> col B C D` .
			show "False" using `\<not> col B C D` `col B C D` by blast
		qed
		hence "F \<noteq> B" by blast
		have "col B C D" using collinear4[OF `axioms` `col F B C` `col F B D` `F \<noteq> B`] .
		show "False" using `col B C D` `\<not> col B C D` by blast
	qed
	hence "E = F" by blast
	thus ?thesis by blast
qed

end