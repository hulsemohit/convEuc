theory diagonalsmeet
	imports Axioms Definitions Theorems
begin

theorem diagonalsmeet:
	assumes: `axioms`
		"parallelogram A B C D"
	shows: "\<exists> M. bet A M C \<and> bet B M D"
proof -
	have "parallel A B C D" sorry
	have "parallel A D B C" sorry
	obtain a b c d m where "A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a m d \<and> bet c m b" sorry
	have "A \<noteq> B" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a m d \<and> bet c m b` by simp
	have "C \<noteq> D" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a m d \<and> bet c m b` by simp
	have "\<not> (meets A B C D)" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a m d \<and> bet c m b` by simp
	have "\<not> (meets A D B C)" sorry
	have "parallel C D A B" using parallelsymmetric[OF `axioms` `parallel A B C D`] .
	have "tarski_parallel C D A B" using paralleldef2B[OF `axioms` `parallel C D A B`] .
	have "same_side A B C D" sorry
	have "D = D" sorry
	have "col D C D" sorry
	have "\<not> (A = D)"
	proof (rule ccontr)
		assume "A = D"
		have "col D C A" sorry
		have "col C D A" using collinearorder[OF `axioms` `col D C A`] by blast
		have "A = A" sorry
		have "col A B A" sorry
		have "meets A B C D" sorry
		show "False" sorry
	qed
	hence "A \<noteq> D" by blast
	obtain E where "bet A D E \<and> seg_eq D E A D" sorry
	have "bet A D E" using `bet A D E \<and> seg_eq D E A D` by simp
	have "\<not> (col D C A)"
	proof (rule ccontr)
		assume "col D C A"
		have "A = A" sorry
		have "col A B A" sorry
		have "col C D A" using collinearorder[OF `axioms` `col D C A`] by blast
		have "meets A B C D" sorry
		have "\<not> (meets A B C D)" sorry
		show "False" sorry
	qed
	hence "\<not> col D C A" by blast
	have "oppo_side A D C E" sorry
	have "same_side A B C D" using `same_side A B C D` .
	have "same_side B A D C" using samesidesymmetric[OF `axioms` `same_side A B C D`] by blast
	have "oppo_side B D C E" using planeseparation[OF `axioms` `same_side B A D C` `oppo_side A D C E`] .
	obtain F where "bet B F E \<and> col D C F \<and> \<not> col D C B" sorry
	have "bet B F E" using `bet B F E \<and> col D C F \<and> \<not> col D C B` by simp
	have "col D C F" using `bet B F E \<and> col D C F \<and> \<not> col D C B` by simp
	have "\<not> col D C B" using `bet B F E \<and> col D C F \<and> \<not> col D C B` by simp
	have "bet E F B" using betweennesssymmetryE[OF `axioms` `bet B F E`] .
	have "bet E D A" using betweennesssymmetryE[OF `axioms` `bet A D E`] .
	have "col E D A" sorry
	have "E \<noteq> D" using betweennotequal[OF `axioms` `bet E D A`] by blast
	have "E \<noteq> A" using betweennotequal[OF `axioms` `bet E D A`] by blast
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "B = C"
		have "col D B C" sorry
		have "col D C B" using collinearorder[OF `axioms` `col D B C`] by blast
		show "False" sorry
	qed
	hence "B \<noteq> C" by blast
	obtain S where "bet B C S \<and> seg_eq C S B C" sorry
	have "bet B C S" using `bet B C S \<and> seg_eq C S B C` by simp
	have "bet S C B" using betweennesssymmetryE[OF `axioms` `bet B C S`] .
	have "col S C B" sorry
	have "S \<noteq> B" using betweennotequal[OF `axioms` `bet S C B`] by blast
	have "C \<noteq> B" using betweennotequal[OF `axioms` `bet S C B`] by blast
