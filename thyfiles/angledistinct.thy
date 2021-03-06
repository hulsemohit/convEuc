theory angledistinct
	imports Geometry equalanglessymmetric
begin

theorem(in euclidean_geometry) angledistinct:
	assumes 
		"ang_eq A B C a b c"
	shows "A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C \<and> a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c"
proof -
	have "\<not> col A B C" using equalangles_f[OF `ang_eq A B C a b c`] by blast
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> B)"
		hence "A = B" by blast
		have "col A B C" using collinear_b `A = B` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> B" by blast
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> C)"
		hence "B = C" by blast
		have "col A B C" using collinear_b `B = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "B \<noteq> C" by blast
	have "\<not> (A = C)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> C)"
		hence "A = C" by blast
		have "col A B C" using collinear_b `A = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> C" by blast
	have "ang_eq a b c A B C" using equalanglessymmetric[OF `ang_eq A B C a b c`] .
	have "\<not> col a b c" using equalangles_f[OF `ang_eq a b c A B C`] by blast
	have "\<not> (a = b)"
	proof (rule ccontr)
		assume "\<not> (a \<noteq> b)"
		hence "a = b" by blast
		have "col a b c" using collinear_b `a = b` by blast
		show "False" using `col a b c` `\<not> col a b c` by blast
	qed
	hence "a \<noteq> b" by blast
	have "\<not> (b = c)"
	proof (rule ccontr)
		assume "\<not> (b \<noteq> c)"
		hence "b = c" by blast
		have "col a b c" using collinear_b `b = c` by blast
		show "False" using `col a b c` `\<not> col a b c` by blast
	qed
	hence "b \<noteq> c" by blast
	have "\<not> (a = c)"
	proof (rule ccontr)
		assume "\<not> (a \<noteq> c)"
		hence "a = c" by blast
		have "col a b c" using collinear_b `a = c` by blast
		show "False" using `col a b c` `\<not> col a b c` by blast
	qed
	hence "a \<noteq> c" by blast
	have "A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C \<and> a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c" using `A \<noteq> B` `B \<noteq> C` `A \<noteq> C` `a \<noteq> b` `b \<noteq> c` `a \<noteq> c` by blast
	thus ?thesis by blast
qed

end