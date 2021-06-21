theory crisscross
	imports Axioms Definitions Theorems
begin

theorem crisscross:
	assumes: `axioms`
		"parallel A C B D"
		"\<not> (cross A B C D)"
	shows: "cross A D B C"
proof -
	have "parallel B D A C" using parallelsymmetric[OF `axioms` `parallel A C B D`] .
	have "tarski_parallel B D A C" using paralleldef2B[OF `axioms` `parallel B D A C`] .
	have "same_side A C B D" sorry
	have "\<not> col A C B" using parallelNC[OF `axioms` `parallel A C B D`] by blast
	have "A \<noteq> B" using NCdistinct[OF `axioms` `\<not> col A C B`] by blast
	obtain E where "bet A B E \<and> seg_eq B E A B" sorry
	have "bet A B E" using `bet A B E \<and> seg_eq B E A B` by simp
	have "B = B" sorry
	have "col B D B" sorry
	have "\<not> col A B D" using parallelNC[OF `axioms` `parallel A C B D`] by blast
	have "\<not> col B D A" using NCorder[OF `axioms` `\<not> col A B D`] by blast
	have "same_side C A B D" using samesidesymmetric[OF `axioms` `same_side A C B D`] by blast
	have "oppo_side A B D E" sorry
	have "oppo_side C B D E" using planeseparation[OF `axioms` `same_side C A B D` `oppo_side A B D E`] .
	obtain F where "bet C F E \<and> col B D F \<and> \<not> col B D C" sorry
	have "bet C F E" using `bet C F E \<and> col B D F \<and> \<not> col B D C` by simp
	have "col B D F" using `bet C F E \<and> col B D F \<and> \<not> col B D C` by simp
	have "\<not> col B D C" using `bet C F E \<and> col B D F \<and> \<not> col B D C` by simp
	have "B \<noteq> D" using NCdistinct[OF `axioms` `\<not> col A B D`] by blast
	have "\<not> col A B D" using parallelNC[OF `axioms` `parallel A C B D`] by blast
	have "A \<noteq> D" using NCdistinct[OF `axioms` `\<not> col A B D`] by blast
	have "\<not> col A C D" using parallelNC[OF `axioms` `parallel A C B D`] by blast
	have "A \<noteq> C" using NCdistinct[OF `axioms` `\<not> col A C B`] by blast
	have "C \<noteq> D" using NCdistinct[OF `axioms` `\<not> col A C D`] by blast
	have "C \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> C`] .
	have "\<not> col A C B" using parallelNC[OF `axioms` `parallel A C B D`] by blast
	have "C \<noteq> B" using NCdistinct[OF `axioms` `\<not> col A C B`] by blast
	have "B \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> B`] .
	have "B = D \<or> B = F \<or> D = F \<or> bet D B F \<or> bet B D F \<or> bet B F D" sorry
