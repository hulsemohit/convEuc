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
	have "A \<noteq> B" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a m d \<and> bet c m b` by blast
	have "C \<noteq> D" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a m d \<and> bet c m b` by blast
	have "\<not> (meets A B C D)" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a m d \<and> bet c m b` by blast
	have "\<not> (meets A D B C)" sorry
	have "parallel C D A B" using parallelsymmetric[OF `axioms` `parallel A B C D`] .
	have "tarski_parallel C D A B" using paralleldef2B[OF `axioms` `parallel C D A B`] .
	have "same_side A B C D" sorry
	have "D = D" using equalityreflexiveE[OF `axioms`] .
	have "col D C D" using col_b `axioms` `D = D` by blast
	have "\<not> (A = D)"
	proof (rule ccontr)
		assume "A = D"
		have "col D C A" sorry
		have "col C D A" using collinearorder[OF `axioms` `col D C A`] by blast
		have "A = A" using equalityreflexiveE[OF `axioms`] .
		have "col A B A" using col_b `axioms` `A = A` by blast
		have "meets A B C D" sorry
		show "False" using `meets A B C D` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a m d \<and> bet c m b` by blast
	qed
	hence "A \<noteq> D" by blast
	obtain E where "bet A D E \<and> seg_eq D E A D" using extensionE[OF `axioms` `A \<noteq> D` `A \<noteq> D`]  by  blast
	have "bet A D E" using `bet A D E \<and> seg_eq D E A D` by blast
	have "\<not> (col D C A)"
	proof (rule ccontr)
		assume "col D C A"
		have "A = A" using equalityreflexiveE[OF `axioms`] .
		have "col A B A" using col_b `axioms` `A = A` by blast
		have "col C D A" using collinearorder[OF `axioms` `col D C A`] by blast
		have "meets A B C D" sorry
		have "\<not> (meets A B C D)" sorry
		show "False" using `\<not> (meets A B C D)` `meets A B C D` by blast
	qed
	hence "\<not> col D C A" by blast
	have "oppo_side A D C E" sorry
	have "same_side A B C D" using `same_side A B C D` .
	have "same_side B A D C" using samesidesymmetric[OF `axioms` `same_side A B C D`] by blast
	have "oppo_side B D C E" using planeseparation[OF `axioms` `same_side B A D C` `oppo_side A D C E`] .
	obtain F where "bet B F E \<and> col D C F \<and> \<not> col D C B" sorry
	have "bet B F E" using `bet B F E \<and> col D C F \<and> \<not> col D C B` by blast
	have "col D C F" using `bet B F E \<and> col D C F \<and> \<not> col D C B` by blast
	have "\<not> col D C B" using `bet B F E \<and> col D C F \<and> \<not> col D C B` by blast
	have "bet E F B" using betweennesssymmetryE[OF `axioms` `bet B F E`] .
	have "bet E D A" using betweennesssymmetryE[OF `axioms` `bet A D E`] .
	have "col E D A" using col_b `axioms` `bet E D A` by blast
	have "E \<noteq> D" using betweennotequal[OF `axioms` `bet E D A`] by blast
	have "E \<noteq> A" using betweennotequal[OF `axioms` `bet E D A`] by blast
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "B = C"
		have "col D B C" using col_b `axioms` `B = C` by blast
		have "col D C B" using collinearorder[OF `axioms` `col D B C`] by blast
		show "False" using `col D C B` `bet B F E \<and> col D C F \<and> \<not> col D C B` by blast
	qed
	hence "B \<noteq> C" by blast
	obtain S where "bet B C S \<and> seg_eq C S B C" using extensionE[OF `axioms` `B \<noteq> C` `B \<noteq> C`]  by  blast
	have "bet B C S" using `bet B C S \<and> seg_eq C S B C` by blast
	have "bet S C B" using betweennesssymmetryE[OF `axioms` `bet B C S`] .
	have "col S C B" using col_b `axioms` `bet S C B` by blast
	have "S \<noteq> B" using betweennotequal[OF `axioms` `bet S C B`] by blast
	have "C \<noteq> B" using betweennotequal[OF `axioms` `bet S C B`] by blast
	have "\<not> (meets E A S B)"
	proof (rule ccontr)
		assume "meets E A S B"
		obtain R where "E \<noteq> A \<and> S \<noteq> B \<and> col E A R \<and> col S B R" sorry
		have "E \<noteq> A" using `E \<noteq> A` .
		have "S \<noteq> B" using `S \<noteq> B` .
		have "col E A R" using `E \<noteq> A \<and> S \<noteq> B \<and> col E A R \<and> col S B R` by blast
		have "col S B R" using `E \<noteq> A \<and> S \<noteq> B \<and> col E A R \<and> col S B R` by blast
		have "col B C S" using col_b `axioms` `bet B C S \<and> seg_eq C S B C` by blast
		have "col S B C" using collinearorder[OF `axioms` `col B C S`] by blast
		consider "B = R"|"B \<noteq> R" by blast
		hence col B C R
		proof (cases)
			case 1
			have "col B C R" using col_b `axioms` `B = R` by blast
		next
			case 2
			have "col B R C" using collinear4[OF `axioms` `col S B R` `col S B C` `S \<noteq> B`] .
			have "col B C R" using collinearorder[OF `axioms` `col B R C`] by blast
		next
		have "col A D E" using col_b `axioms` `bet A D E \<and> seg_eq D E A D` by blast
		have "col E A D" using collinearorder[OF `axioms` `col A D E`] by blast
		have "A \<noteq> D" using betweennotequal[OF `axioms` `bet A D E`] by blast
		have "col A D R" using collinear4[OF `axioms` `col E A D` `col E A R` `E \<noteq> A`] .
		have "A \<noteq> D \<and> B \<noteq> C \<and> col A D R \<and> col B C R" using `A \<noteq> D` `B \<noteq> C` `col A D R` `col B C R` by blast
		have "meets A D B C" sorry
		show "False" using `meets A D B C` `\<not> (meets A D B C)` by blast
	qed
	hence "\<not> (meets E A S B)" by blast
	have "bet D F C" using collinearbetween[OF `axioms` `col E D A` `col S C B` `E \<noteq> A` `S \<noteq> B` `E \<noteq> D` `C \<noteq> B` `\<not> (meets E A S B)` `bet E F B` `col D C F`] .
	have "bet C F D" using betweennesssymmetryE[OF `axioms` `bet D F C`] .
	have "A \<noteq> E" using betweennotequal[OF `axioms` `bet A D E`] by blast
	have "E \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> E`] .
	have "B \<noteq> S" using betweennotequal[OF `axioms` `bet B C S`] by blast
	have "S \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> S`] .
	have "\<not> (col E A C)"
	proof (rule ccontr)
		assume "col E A C"
		have "col B C S" using col_b `axioms` `bet B C S \<and> seg_eq C S B C` by blast
		have "col S B C" using collinearorder[OF `axioms` `col B C S`] by blast
		have "E \<noteq> A \<and> S \<noteq> B \<and> col E A C \<and> col S B C" using `E \<noteq> A` `S \<noteq> B` `col E A C` `col S B C` by blast
		have "meets E A S B" sorry
		have "\<not> (meets E A S B)" using `\<not> (meets E A S B)` .
		show "False" using `\<not> (meets E A S B)` `meets E A S B` by blast
	qed
	hence "\<not> col E A C" by blast
	obtain H where "bet C H A \<and> bet E F H" using Pasch-outerE[OF `axioms` `bet C F D` `bet E D A` `\<not> col E A C`]  by  blast
	have "bet C H A" using `bet C H A \<and> bet E F H` by blast
	have "bet E F H" using `bet C H A \<and> bet E F H` by blast
	have "col E F H" using col_b `axioms` `bet C H A \<and> bet E F H` by blast
	have "col E F B" using col_b `axioms` `bet E F B` by blast
	have "E \<noteq> F" using betweennotequal[OF `axioms` `bet E F B`] by blast
	have "F \<noteq> E" using inequalitysymmetric[OF `axioms` `E \<noteq> F`] .
	have "col F E H" using collinearorder[OF `axioms` `col E F H`] by blast
	have "col F E B" using collinearorder[OF `axioms` `col E F B`] by blast
	have "col E H B" using collinear4[OF `axioms` `col F E H` `col F E B` `F \<noteq> E`] .
	have "bet A H C" using betweennesssymmetryE[OF `axioms` `bet C H A`] .
	have "A \<noteq> E" using `A \<noteq> E` .
	obtain R where "bet A E R \<and> seg_eq E R A E" using extensionE[OF `axioms` `A \<noteq> E` `A \<noteq> E`]  by  blast
	have "bet A E R" using `bet A E R \<and> seg_eq E R A E` by blast
	have "col A E R" using col_b `axioms` `bet A E R \<and> seg_eq E R A E` by blast
	have "A \<noteq> E" using betweennotequal[OF `axioms` `bet A D E`] by blast
	have "A \<noteq> R" using betweennotequal[OF `axioms` `bet A E R`] by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> C`] .
	obtain T where "bet C B T \<and> seg_eq B T C B" using extensionE[OF `axioms` `C \<noteq> B` `C \<noteq> B`]  by  blast
	have "bet C B T" using `bet C B T \<and> seg_eq B T C B` by blast
	have "\<not> (meets A R T C)"
	proof (rule ccontr)
		assume "meets A R T C"
		obtain p where "A \<noteq> R \<and> T \<noteq> C \<and> col A R p \<and> col T C p" sorry
		have "A \<noteq> R" using `A \<noteq> R` .
		have "T \<noteq> C" using `A \<noteq> R \<and> T \<noteq> C \<and> col A R p \<and> col T C p` by blast
		have "col A R p" using `A \<noteq> R \<and> T \<noteq> C \<and> col A R p \<and> col T C p` by blast
		have "col T C p" using `A \<noteq> R \<and> T \<noteq> C \<and> col A R p \<and> col T C p` by blast
		have "col C B T" using col_b `axioms` `bet C B T \<and> seg_eq B T C B` by blast
		have "col A D E" using col_b `axioms` `bet A D E \<and> seg_eq D E A D` by blast
		have "A = A" using equalityreflexiveE[OF `axioms`] .
		have "col A R A" using col_b `axioms` `A = A` by blast
		have "col E A D" using collinearorder[OF `axioms` `col A D E`] by blast
		have "col A E R" using col_b `axioms` `bet A E R \<and> seg_eq E R A E` by blast
		have "col E A R" using collinearorder[OF `axioms` `col A E R`] by blast
		have "A \<noteq> D" using betweennotequal[OF `axioms` `bet A D E`] by blast
		have "col A D R" using collinear4[OF `axioms` `col E A D` `col E A R` `E \<noteq> A`] .
		have "col A R D" using collinearorder[OF `axioms` `col A D R`] by blast
		have "col A D p" using collinear5[OF `axioms` `A \<noteq> R` `col A R A` `col A R D` `col A R p`] .
		have "col B T C" using collinearorder[OF `axioms` `col C B T`] by blast
		have "col T C B" using collinearorder[OF `axioms` `col B T C`] by blast
		have "C \<noteq> T" using betweennotequal[OF `axioms` `bet C B T`] by blast
		have "T \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> T`] .
		have "col C B p" using collinear4[OF `axioms` `col T C B` `col T C p` `T \<noteq> C`] .
		have "col B C p" using collinearorder[OF `axioms` `col C B p`] by blast
		have "A \<noteq> D \<and> B \<noteq> C \<and> col A D p \<and> col B C p" using `A \<noteq> D` `B \<noteq> C` `col A D p` `col B C p` by blast
		have "meets A D B C" sorry
		have "\<not> (meets A D B C)" using `\<not> (meets A D B C)` .
		show "False" using `\<not> (meets A D B C)` `meets A D B C` by blast
	qed
	hence "\<not> (meets A R T C)" by blast
	have "bet T B C" using betweennesssymmetryE[OF `axioms` `bet C B T`] .
	have "col T B C" using col_b `axioms` `bet T B C` by blast
	have "T \<noteq> C" using betweennotequal[OF `axioms` `bet T B C`] by blast
	have "B \<noteq> C" using betweennotequal[OF `axioms` `bet B C S`] by blast
	have "bet A H C" using `bet A H C` .
	have "col E B H" using collinearorder[OF `axioms` `col E H B`] by blast
	have "bet E H B" using collinearbetween[OF `axioms` `col A E R` `col T B C` `A \<noteq> R` `T \<noteq> C` `A \<noteq> E` `B \<noteq> C` `\<not> (meets A R T C)` `bet A H C` `col E B H`] .
	have "bet B H E" using betweennesssymmetryE[OF `axioms` `bet E H B`] .
	have "bet A D E" using `bet A D E` .
	have "\<not> (col B E A)"
	proof (rule ccontr)
		assume "col B E A"
		have "col A D E" using col_b `axioms` `bet A D E \<and> seg_eq D E A D` by blast
		have "col E A D" using collinearorder[OF `axioms` `col A D E`] by blast
		have "col E A B" using collinearorder[OF `axioms` `col B E A`] by blast
		have "col A D B" using collinear4[OF `axioms` `col E A D` `col E A B` `E \<noteq> A`] .
		have "B = B" using equalityreflexiveE[OF `axioms`] .
		have "col B C B" using col_b `axioms` `B = B` by blast
		have "A \<noteq> D \<and> B \<noteq> C \<and> col A D B \<and> col B C B" using `A \<noteq> D` `B \<noteq> C` `col A D B` `col B C B` by blast
		have "meets A D B C" sorry
		show "False" using `meets A D B C` `\<not> (meets A D B C)` by blast
	qed
	hence "\<not> col B E A" by blast
	obtain M where "bet B M D \<and> bet A M H" using Pasch-innerE[OF `axioms` `bet B H E` `bet A D E` `\<not> col B E A`]  by  blast
	have "bet B M D" using `bet B M D \<and> bet A M H` by blast
	have "bet A M H" using `bet B M D \<and> bet A M H` by blast
	have "bet A H C" using betweennesssymmetryE[OF `axioms` `bet C H A`] .
	have "bet A M C" using n3_6b[OF `axioms` `bet A M H` `bet A H C`] .
	have "bet A M C \<and> bet B M D" using `bet A M C` `bet B M D \<and> bet A M H` by blast
	thus ?thesis by blast
qed

end