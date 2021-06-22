theory angledistinct
	imports Axioms Definitions Theorems
begin

theorem angledistinct:
	assumes: `axioms`
		"ang_eq A B C a b c"
	shows: "A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C \<and> a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c"
proof -
	have "\<not> col A B C" using equalangles_f[OF `axioms` `ang_eq A B C a b c`] by blast
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "A = B"
		have "col A B C" using collinear_b `axioms` `A = B` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> B" by blast
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "B = C"
		have "col A B C" using collinear_b `axioms` `B = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "B \<noteq> C" by blast
	have "\<not> (A = C)"
	proof (rule ccontr)
		assume "A = C"
		have "col A B C" using collinear_b `axioms` `A = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> C" by blast
	have "ang_eq a b c A B C" using equalanglessymmetric[OF `axioms` `ang_eq A B C a b c`] .
	have "\<not> col a b c" using equalangles_f[OF `axioms` `ang_eq a b c A B C`] by blast
	have "\<not> (a = b)"
	proof (rule ccontr)
		assume "a = b"
		have "col a b c" using collinear_b `axioms` `a = b` by blast
		show "False" using `col a b c` `\<not> col a b c` by blast
	qed
	hence "a \<noteq> b" by blast
	have "\<not> (b = c)"
	proof (rule ccontr)
		assume "b = c"
		have "col a b c" using collinear_b `axioms` `b = c` by blast
		show "False" using `col a b c` `\<not> col a b c` by blast
	qed
	hence "b \<noteq> c" by blast
	have "\<not> (a = c)"
	proof (rule ccontr)
		assume "a = c"
		have "col a b c" using collinear_b `axioms` `a = c` by blast
		show "False" using `col a b c` `\<not> col a b c` by blast
	qed
	hence "a \<noteq> c" by blast
	have "A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C \<and> a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c" using `A \<noteq> B` `B \<noteq> C` `A \<noteq> C` `a \<noteq> b` `b \<noteq> c` `a \<noteq> c` by blast
	thus ?thesis by blast
qed

end