theory parallelNC
	imports Axioms Definitions Theorems
begin

theorem parallelNC:
	assumes: `axioms`
		"parallel A B C D"
	shows: "\<not> col A B C \<and> \<not> col A C D \<and> \<not> col B C D \<and> \<not> col A B D"
proof -
	obtain M a b c d where "A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b" sorry
	have "A \<noteq> B" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	have "C \<noteq> D" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	have "\<not> (meets A B C D)" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	have "\<not> (col A C D)"
	proof (rule ccontr)
		assume "col A C D"
		have "col C D A" using collinearorder[OF `axioms` `col A C D`] by blast
		have "A = A" using equalityreflexiveE[OF `axioms`] .
		have "col A B A" using col_b `axioms` `A = A` by blast
		have "A \<noteq> B \<and> C \<noteq> D \<and> col A B A \<and> col C D A" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `col A B A` `col C D A` by blast
		have "meets A B C D" sorry
		show "False" using `meets A B C D` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	qed
	hence "\<not> col A C D" by blast
	have "\<not> (col A B C)"
	proof (rule ccontr)
		assume "col A B C"
		have "C = C" using equalityreflexiveE[OF `axioms`] .
		have "col C D C" using col_b `axioms` `C = C` by blast
		have "A \<noteq> B \<and> C \<noteq> D \<and> col A B C \<and> col C D C" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `col A B C` `col C D C` by blast
		have "meets A B C D" sorry
		show "False" using `meets A B C D` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	qed
	hence "\<not> col A B C" by blast
	have "\<not> (col B C D)"
	proof (rule ccontr)
		assume "col B C D"
		have "col C D B" using collinearorder[OF `axioms` `col B C D`] by blast
		have "B = B" using equalityreflexiveE[OF `axioms`] .
		have "col A B B" using col_b `axioms` `B = B` by blast
		have "A \<noteq> B \<and> C \<noteq> D \<and> col A B B \<and> col C D B" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `col A B B` `col C D B` by blast
		have "meets A B C D" sorry
		show "False" using `meets A B C D` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	qed
	hence "\<not> col B C D" by blast
	have "\<not> (col A B D)"
	proof (rule ccontr)
		assume "col A B D"
		have "D = D" using equalityreflexiveE[OF `axioms`] .
		have "col C D D" using col_b `axioms` `D = D` by blast
		have "A \<noteq> B \<and> C \<noteq> D \<and> col A B D \<and> col C D D" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `col A B D` `col C D D` by blast
		have "meets A B C D" sorry
		show "False" using `meets A B C D` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	qed
	hence "\<not> col A B D" by blast
	have "\<not> col A B C \<and> \<not> col A C D \<and> \<not> col B C D \<and> \<not> col A B D" using `\<not> col A B C` `\<not> col A C D` `\<not> col B C D` `\<not> col A B D` by blast
	thus ?thesis by blast
qed

end