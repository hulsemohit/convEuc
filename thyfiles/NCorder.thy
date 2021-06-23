theory NCorder
	imports Geometry collinearorder
begin

theorem NCorder:
	assumes "axioms"
		"\<not> col A B C"
	shows "\<not> col B A C \<and> \<not> col B C A \<and> \<not> col C A B \<and> \<not> col A C B \<and> \<not> col C B A"
proof -
	have "\<not> (col B A C)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col B A C))"
hence "col B A C" by blast
		have "col A B C" using collinearorder[OF `axioms` `col B A C`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col B A C" by blast
	have "\<not> (col B C A)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col B C A))"
hence "col B C A" by blast
		have "col A B C" using collinearorder[OF `axioms` `col B C A`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col B C A" by blast
	have "\<not> (col C A B)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col C A B))"
hence "col C A B" by blast
		have "col A B C" using collinearorder[OF `axioms` `col C A B`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col C A B" by blast
	have "\<not> (col A C B)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col A C B))"
hence "col A C B" by blast
		have "col A B C" using collinearorder[OF `axioms` `col A C B`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col A C B" by blast
	have "\<not> (col C B A)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col C B A))"
hence "col C B A" by blast
		have "col A B C" using collinearorder[OF `axioms` `col C B A`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col C B A" by blast
	have "\<not> col B A C \<and> \<not> col B C A \<and> \<not> col C A B \<and> \<not> col A C B \<and> \<not> col C B A" using `\<not> col B A C` `\<not> col B C A` `\<not> col C A B` `\<not> col A C B` `\<not> col C B A` by blast
	thus ?thesis by blast
qed

end