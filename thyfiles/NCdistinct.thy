theory NCdistinct
	imports Geometry inequalitysymmetric
begin

theorem(in euclidean_geometry) NCdistinct:
	assumes 
		"\<not> col A B C"
	shows "A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C \<and> B \<noteq> A \<and> C \<noteq> B \<and> C \<noteq> A"
proof -
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> B)"
		hence "A = B" by blast
		have "col A B C" using collinear_b `A = B` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> B" by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
	have "\<not> (A = C)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> C)"
		hence "A = C" by blast
		have "col A B C" using collinear_b `A = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> C" by blast
	have "C \<noteq> A" using inequalitysymmetric[OF `A \<noteq> C`] .
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> C)"
		hence "B = C" by blast
		have "col A B C" using collinear_b `B = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "B \<noteq> C" by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `B \<noteq> C`] .
	have "A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C \<and> B \<noteq> A \<and> C \<noteq> B \<and> C \<noteq> A" using `A \<noteq> B` `B \<noteq> C` `A \<noteq> C` `B \<noteq> A` `C \<noteq> B` `C \<noteq> A` by blast
	thus ?thesis by blast
qed

end