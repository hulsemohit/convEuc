theory parallelflip
	imports Axioms Definitions Theorems
begin

theorem parallelflip:
	assumes: `axioms`
		"parallel A B C D"
	shows: "parallel B A C D \<and> parallel A B D C \<and> parallel B A D C"
proof -
	obtain M a b c d where "A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b" sorry
	have "A \<noteq> B" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	have "C \<noteq> D" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	have "col A B a" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	have "col A B b" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	have "a \<noteq> b" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	have "col C D c" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	have "col C D d" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	have "c \<noteq> d" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	have "\<not> (meets A B C D)" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	have "bet a M d" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	have "bet c M b" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	have "col B A a" using collinearorder[OF `axioms` `col A B a`] by blast
	have "col B A b" using collinearorder[OF `axioms` `col A B b`] by blast
	have "col D C c" using collinearorder[OF `axioms` `col C D c`] by blast
	have "col D C d" using collinearorder[OF `axioms` `col C D d`] by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	have "D \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> D`] .
	have "bet d M a" using betweennesssymmetryE[OF `axioms` `bet a M d`] .
	have "bet b M c" using betweennesssymmetryE[OF `axioms` `bet c M b`] .
	have "d \<noteq> c" using inequalitysymmetric[OF `axioms` `c \<noteq> d`] .
	have "b \<noteq> a" using inequalitysymmetric[OF `axioms` `a \<noteq> b`] .
	have "\<not> (meets A B D C)"
	proof (rule ccontr)
		assume "meets A B D C"
		obtain P where "A \<noteq> B \<and> D \<noteq> C \<and> col A B P \<and> col D C P" sorry
		have "col A B P" using `A \<noteq> B \<and> D \<noteq> C \<and> col A B P \<and> col D C P` by blast
		have "col D C P" using `A \<noteq> B \<and> D \<noteq> C \<and> col A B P \<and> col D C P` by blast
		have "col C D P" using collinearorder[OF `axioms` `col D C P`] by blast
		have "A \<noteq> B \<and> D \<noteq> C \<and> col A B P \<and> col C D P" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `A \<noteq> B \<and> D \<noteq> C \<and> col A B P \<and> col D C P` `A \<noteq> B \<and> D \<noteq> C \<and> col A B P \<and> col D C P` `col C D P` by blast
		have "meets A B C D" sorry
		show "False" using `meets A B C D` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	qed
	hence "\<not> (meets A B D C)" by blast
	have "\<not> (meets B A C D)"
	proof (rule ccontr)
		assume "meets B A C D"
		obtain P where "B \<noteq> A \<and> C \<noteq> D \<and> col B A P \<and> col C D P" sorry
		have "col B A P" using `B \<noteq> A \<and> C \<noteq> D \<and> col B A P \<and> col C D P` by blast
		have "col C D P" using `B \<noteq> A \<and> C \<noteq> D \<and> col B A P \<and> col C D P` by blast
		have "col A B P" using collinearorder[OF `axioms` `col B A P`] by blast
		have "A \<noteq> B \<and> C \<noteq> D \<and> col B A P \<and> col C D P" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `B \<noteq> A \<and> C \<noteq> D \<and> col B A P \<and> col C D P` `B \<noteq> A \<and> C \<noteq> D \<and> col B A P \<and> col C D P` by blast
		have "meets A B C D" sorry
		show "False" using `meets A B C D` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	qed
	hence "\<not> (meets B A C D)" by blast
	have "\<not> (meets B A D C)"
	proof (rule ccontr)
		assume "meets B A D C"
		obtain P where "B \<noteq> A \<and> D \<noteq> C \<and> col B A P \<and> col D C P" sorry
		have "col B A P" using `B \<noteq> A \<and> D \<noteq> C \<and> col B A P \<and> col D C P` by blast
		have "col D C P" using `B \<noteq> A \<and> D \<noteq> C \<and> col B A P \<and> col D C P` by blast
		have "col A B P" using collinearorder[OF `axioms` `col B A P`] by blast
		have "col C D P" using collinearorder[OF `axioms` `col D C P`] by blast
		have "A \<noteq> B \<and> C \<noteq> D \<and> col A B P \<and> col C D P" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `col A B P` `col C D P` by blast
		have "meets A B C D" sorry
		show "False" using `meets A B C D` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	qed
	hence "\<not> (meets B A D C)" by blast
	have "B \<noteq> A \<and> C \<noteq> D \<and> col B A a \<and> col B A b \<and> b \<noteq> a \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets B A C D) \<and> bet a M d \<and> bet c M b" using `B \<noteq> A` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `col B A a` `col B A b` `b \<noteq> a` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `\<not> (meets B A C D)` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	have "parallel B A C D" sorry
	have "A \<noteq> B \<and> D \<noteq> C \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col D C c \<and> col D C d \<and> d \<noteq> c \<and> \<not> (meets A B D C) \<and> bet a M d \<and> bet c M b" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `D \<noteq> C` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `col D C c` `col D C d` `d \<noteq> c` `\<not> (meets A B D C)` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	have "parallel A B D C" sorry
	have "B \<noteq> A \<and> D \<noteq> C \<and> col B A a \<and> col B A b \<and> b \<noteq> a \<and> col D C c \<and> col D C d \<and> d \<noteq> c \<and> \<not> (meets B A D C) \<and> bet a M d \<and> bet c M b" using `B \<noteq> A \<and> C \<noteq> D \<and> col B A a \<and> col B A b \<and> b \<noteq> a \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets B A C D) \<and> bet a M d \<and> bet c M b` `A \<noteq> B \<and> D \<noteq> C \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col D C c \<and> col D C d \<and> d \<noteq> c \<and> \<not> (meets A B D C) \<and> bet a M d \<and> bet c M b` `B \<noteq> A \<and> C \<noteq> D \<and> col B A a \<and> col B A b \<and> b \<noteq> a \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets B A C D) \<and> bet a M d \<and> bet c M b` `B \<noteq> A \<and> C \<noteq> D \<and> col B A a \<and> col B A b \<and> b \<noteq> a \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets B A C D) \<and> bet a M d \<and> bet c M b` `B \<noteq> A \<and> C \<noteq> D \<and> col B A a \<and> col B A b \<and> b \<noteq> a \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets B A C D) \<and> bet a M d \<and> bet c M b` `A \<noteq> B \<and> D \<noteq> C \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col D C c \<and> col D C d \<and> d \<noteq> c \<and> \<not> (meets A B D C) \<and> bet a M d \<and> bet c M b` `A \<noteq> B \<and> D \<noteq> C \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col D C c \<and> col D C d \<and> d \<noteq> c \<and> \<not> (meets A B D C) \<and> bet a M d \<and> bet c M b` `A \<noteq> B \<and> D \<noteq> C \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col D C c \<and> col D C d \<and> d \<noteq> c \<and> \<not> (meets A B D C) \<and> bet a M d \<and> bet c M b` `\<not> (meets B A D C)` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a M d \<and> bet c M b` by blast
	have "parallel B A D C" sorry
	have "parallel B A C D \<and> parallel A B D C \<and> parallel B A D C" using `parallel B A C D` `parallel A B D C` `parallel B A D C` by blast
	thus ?thesis by blast
qed

end