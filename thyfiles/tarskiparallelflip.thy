theory tarskiparallelflip
	imports Geometry collinearorder inequalitysymmetric samesidesymmetric
begin

theorem tarskiparallelflip:
	assumes "axioms"
		"tarski_parallel A B C D"
	shows "tarski_parallel B A C D \<and> tarski_parallel A B D C \<and> tarski_parallel B A D C"
proof -
	have "A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B" using tarski_parallel_f[OF `axioms` `tarski_parallel A B C D`] .
	have "A \<noteq> B" using `A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B` by blast
	have "C \<noteq> D" using `A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B` by blast
	have "\<not> (meets A B C D)" using `A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B` by blast
	have "same_side C D A B" using `A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B` by blast
	have "same_side D C A B" using samesidesymmetric[OF `axioms` `same_side C D A B`] by blast
	have "D \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> D`] .
	have "\<not> (meets A B D C)"
	proof (rule ccontr)
		assume "\<not> (\<not> (meets A B D C))"
hence "meets A B D C" by blast
		obtain T where "A \<noteq> B \<and> D \<noteq> C \<and> col A B T \<and> col D C T" using meet_f[OF `axioms` `meets A B D C`]  by  blast
		have "A \<noteq> B" using `A \<noteq> B` .
		have "D \<noteq> C" using `D \<noteq> C` .
		have "col A B T" using `A \<noteq> B \<and> D \<noteq> C \<and> col A B T \<and> col D C T` by blast
		have "col D C T" using `A \<noteq> B \<and> D \<noteq> C \<and> col A B T \<and> col D C T` by blast
		have "col C D T" using collinearorder[OF `axioms` `col D C T`] by blast
		have "C \<noteq> D" using inequalitysymmetric[OF `axioms` `D \<noteq> C`] .
		have "A \<noteq> B \<and> C \<noteq> D \<and> col A B T \<and> col C D T" using `A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B` `A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B` `A \<noteq> B \<and> D \<noteq> C \<and> col A B T \<and> col D C T` `col C D T` by blast
		have "meets A B C D" using meet_b[OF `axioms` `A \<noteq> B` `C \<noteq> D` `col A B T` `col C D T`] .
		show "False" using `meets A B C D` `A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B` by blast
	qed
	hence "\<not> (meets A B D C)" by blast
	have "A \<noteq> B \<and> D \<noteq> C \<and> \<not> (meets A B D C) \<and> same_side D C A B" using `A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B` `D \<noteq> C` `\<not> (meets A B D C)` `same_side D C A B` by blast
	have "tarski_parallel A B D C" using tarski_parallel_b[OF `axioms` `A \<noteq> B` `D \<noteq> C` `\<not> (meets A B D C)` `same_side D C A B`] .
	have "\<not> (meets B A C D)"
	proof (rule ccontr)
		assume "\<not> (\<not> (meets B A C D))"
hence "meets B A C D" by blast
		obtain T where "B \<noteq> A \<and> C \<noteq> D \<and> col B A T \<and> col C D T" using meet_f[OF `axioms` `meets B A C D`]  by  blast
		have "C \<noteq> D" using `C \<noteq> D` .
		have "col B A T" using `B \<noteq> A \<and> C \<noteq> D \<and> col B A T \<and> col C D T` by blast
		have "col C D T" using `B \<noteq> A \<and> C \<noteq> D \<and> col B A T \<and> col C D T` by blast
		have "col A B T" using collinearorder[OF `axioms` `col B A T`] by blast
		have "meets A B C D" using meet_b[OF `axioms` `A \<noteq> B` `C \<noteq> D` `col A B T` `col C D T`] .
		show "False" using `meets A B C D` `A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B` by blast
	qed
	hence "\<not> (meets B A C D)" by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	have "same_side C D B A" using samesidesymmetric[OF `axioms` `same_side C D A B`] by blast
	have "same_side D C B A" using samesidesymmetric[OF `axioms` `same_side C D A B`] by blast
	have "B \<noteq> A \<and> C \<noteq> D \<and> \<not> (meets B A C D) \<and> same_side C D B A" using `B \<noteq> A` `A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B` `\<not> (meets B A C D)` `same_side C D B A` by blast
	have "tarski_parallel B A C D" using tarski_parallel_b[OF `axioms` `B \<noteq> A` `C \<noteq> D` `\<not> (meets B A C D)` `same_side C D B A`] .
	have "\<not> (meets B A D C)"
	proof (rule ccontr)
		assume "\<not> (\<not> (meets B A D C))"
hence "meets B A D C" by blast
		obtain T where "B \<noteq> A \<and> D \<noteq> C \<and> col B A T \<and> col D C T" using meet_f[OF `axioms` `meets B A D C`]  by  blast
		have "C \<noteq> D" using `C \<noteq> D` .
		have "col B A T" using `B \<noteq> A \<and> D \<noteq> C \<and> col B A T \<and> col D C T` by blast
		have "col D C T" using `B \<noteq> A \<and> D \<noteq> C \<and> col B A T \<and> col D C T` by blast
		have "col A B T" using collinearorder[OF `axioms` `col B A T`] by blast
		have "col C D T" using collinearorder[OF `axioms` `col D C T`] by blast
		have "meets A B C D" using meet_b[OF `axioms` `A \<noteq> B` `C \<noteq> D` `col A B T` `col C D T`] .
		show "False" using `meets A B C D` `A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B` by blast
	qed
	hence "\<not> (meets B A D C)" by blast
	have "B \<noteq> A \<and> D \<noteq> C \<and> \<not> (meets B A D C) \<and> same_side D C B A" using `B \<noteq> A \<and> C \<noteq> D \<and> \<not> (meets B A C D) \<and> same_side C D B A` `A \<noteq> B \<and> D \<noteq> C \<and> \<not> (meets A B D C) \<and> same_side D C A B` `\<not> (meets B A D C)` `same_side D C B A` by blast
	have "tarski_parallel B A D C" using tarski_parallel_b[OF `axioms` `B \<noteq> A` `D \<noteq> C` `\<not> (meets B A D C)` `same_side D C B A`] .
	have "tarski_parallel B A C D \<and> tarski_parallel A B D C \<and> tarski_parallel B A D C" using `tarski_parallel B A C D` `tarski_parallel A B D C` `tarski_parallel B A D C` by blast
	thus ?thesis by blast
qed

end