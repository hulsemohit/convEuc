theory paralleldef2B
	imports n3_7b Geometry betweennotequal collinear4 collinear5 collinearorder inequalitysymmetric parallelcollinear tarskiparallelflip
begin

theorem paralleldef2B:
	assumes "axioms"
		"parallel A B C D"
	shows "tarski_parallel A B C D"
proof -
	obtain a b c d e where "A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a e d \<and> bet c e b" using parallel_f[OF `axioms` `parallel A B C D`]  by  blast
	have "col A B b" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a e d \<and> bet c e b` by blast
	have "a \<noteq> b" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a e d \<and> bet c e b` by blast
	have "col C D c" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a e d \<and> bet c e b` by blast
	have "col C D d" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a e d \<and> bet c e b` by blast
	have "c \<noteq> d" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a e d \<and> bet c e b` by blast
	have "\<not> (meets A B C D)" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a e d \<and> bet c e b` by blast
	have "A \<noteq> B" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a e d \<and> bet c e b` by blast
	have "C \<noteq> D" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a e d \<and> bet c e b` by blast
	have "bet a e d" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a e d \<and> bet c e b` by blast
	have "bet c e b" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a e d \<and> bet c e b` by blast
	have "b \<noteq> a" using inequalitysymmetric[OF `axioms` `a \<noteq> b`] .
	have "e \<noteq> b" using betweennotequal[OF `axioms` `bet c e b`] by blast
	have "\<not> (meets a b C D)"
	proof (rule ccontr)
		assume "\<not> (\<not> (meets a b C D))"
hence "meets a b C D" by blast
		obtain R where "a \<noteq> b \<and> C \<noteq> D \<and> col a b R \<and> col C D R" using meet_f[OF `axioms` `meets a b C D`]  by  blast
		have "col a b R" using `a \<noteq> b \<and> C \<noteq> D \<and> col a b R \<and> col C D R` by blast
		have "col C D R" using `a \<noteq> b \<and> C \<noteq> D \<and> col a b R \<and> col C D R` by blast
		have "col b a R" using collinearorder[OF `axioms` `col a b R`] by blast
		have "col A B a" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a e d \<and> bet c e b` by blast
		have "col A B b" using `col A B b` .
		have "col B a b" using collinear4[OF `axioms` `col A B a` `col A B b` `A \<noteq> B`] .
		have "col b a B" using collinearorder[OF `axioms` `col B a b`] by blast
		have "col a B R" using collinear4[OF `axioms` `col b a B` `col b a R` `b \<noteq> a`] .
		have "col a B A" using collinearorder[OF `axioms` `col A B a`] by blast
		consider "a \<noteq> B"|"a = B" by blast
		hence "col A B R"
		proof (cases)
			assume "a \<noteq> B"
			have "col B R A" using collinear4[OF `axioms` `col a B R` `col a B A` `a \<noteq> B`] .
			have "col A B R" using collinearorder[OF `axioms` `col B R A`] by blast
			thus ?thesis by blast
		next
			assume "a = B"
			have "col B A a" using collinearorder[OF `axioms` `col A B a`] by blast
			have "col B A b" using collinearorder[OF `axioms` `col A B b`] by blast
			have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
			have "col A a b" using collinear4[OF `axioms` `col B A a` `col B A b` `B \<noteq> A`] .
			have "col b a A" using collinearorder[OF `axioms` `col A a b`] by blast
			have "col b a R" using `col b a R` .
			have "col a A R" using collinear4[OF `axioms` `col b a A` `col b a R` `b \<noteq> a`] .
			have "col a A B" using collinearorder[OF `axioms` `col A B a`] by blast
			have "A \<noteq> a" using `A \<noteq> B` `a = B` by blast
			have "a \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> a`] .
			have "col A R B" using collinear4[OF `axioms` `col a A R` `col a A B` `a \<noteq> A`] .
			have "col A B R" using collinearorder[OF `axioms` `col A R B`] by blast
			thus ?thesis by blast
		qed
		have "col C D R" using `col C D R` .
		have "A \<noteq> B \<and> C \<noteq> D \<and> col A B R \<and> col C D R" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a e d \<and> bet c e b` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a e d \<and> bet c e b` `col A B R` `a \<noteq> b \<and> C \<noteq> D \<and> col a b R \<and> col C D R` by blast
		have "meets A B C D" using meet_b[OF `axioms` `A \<noteq> B` `C \<noteq> D` `col A B R` `col C D R`] .
		have "\<not> (meets A B C D)" using `\<not> (meets A B C D)` .
		show "False" using `\<not> (meets A B C D)` `meets A B C D` by blast
	qed
	hence "\<not> (meets a b C D)" by blast
	obtain P where "bet e b P \<and> seg_eq b P e b" using extensionE[OF `axioms` `e \<noteq> b` `e \<noteq> b`]  by  blast
	have "bet e b P" using `bet e b P \<and> seg_eq b P e b` by blast
	have "bet P b e" using betweennesssymmetryE[OF `axioms` `bet e b P`] .
	have "bet b e c" using betweennesssymmetryE[OF `axioms` `bet c e b`] .
	have "bet P b c" using n3_7b[OF `axioms` `bet P b e` `bet b e c`] .
	have "bet c b P" using betweennesssymmetryE[OF `axioms` `bet P b c`] .
	have "\<not> (col a d P)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col a d P))"
hence "col a d P" by blast
		have "col a e d" using collinear_b `axioms` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a e d \<and> bet c e b` by blast
		have "col a d e" using collinearorder[OF `axioms` `col a e d`] by blast
		have "a \<noteq> d" using betweennotequal[OF `axioms` `bet a e d`] by blast
		have "col d P e" using collinear4[OF `axioms` `col a d P` `col a d e` `a \<noteq> d`] .
		have "col e P d" using collinearorder[OF `axioms` `col d P e`] by blast
		have "col e b P" using collinear_b `axioms` `bet e b P \<and> seg_eq b P e b` by blast
		have "col e P b" using collinearorder[OF `axioms` `col e b P`] by blast
		have "e \<noteq> P" using betweennotequal[OF `axioms` `bet e b P`] by blast
		have "col P d b" using collinear4[OF `axioms` `col e P d` `col e P b` `e \<noteq> P`] .
		have "col d P b" using collinearorder[OF `axioms` `col P d b`] by blast
		have "col d P a" using collinearorder[OF `axioms` `col a d P`] by blast
		have "\<not> (d = P)"
		proof (rule ccontr)
			assume "\<not> (d \<noteq> P)"
			hence "d = P" by blast
			have "col c b P" using collinear_b `axioms` `bet c b P` by blast
			have "col c b d" using `col c b P` `d = P` by blast
			have "col b e c" using collinear_b `axioms` `bet b e c` by blast
			have "col c b e" using collinearorder[OF `axioms` `col b e c`] by blast
			have "c \<noteq> b" using betweennotequal[OF `axioms` `bet c b P`] by blast
			have "col b d e" using collinear4[OF `axioms` `col c b d` `col c b e` `c \<noteq> b`] .
			have "col d e a" using collinearorder[OF `axioms` `col a d e`] by blast
			have "col d e b" using collinearorder[OF `axioms` `col b d e`] by blast
			have "e \<noteq> d" using betweennotequal[OF `axioms` `bet a e d`] by blast
			have "d \<noteq> e" using inequalitysymmetric[OF `axioms` `e \<noteq> d`] .
			have "col e a b" using collinear4[OF `axioms` `col d e a` `col d e b` `d \<noteq> e`] .
			have "col a e d" using collinear_b `axioms` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a e d \<and> bet c e b` by blast
			have "col e a d" using collinearorder[OF `axioms` `col a d e`] by blast
			have "a \<noteq> e" using betweennotequal[OF `axioms` `bet a e d`] by blast
			have "e \<noteq> a" using inequalitysymmetric[OF `axioms` `a \<noteq> e`] .
			have "col a b d" using collinear4[OF `axioms` `col e a b` `col e a d` `e \<noteq> a`] .
			have "col C D d" using `col C D d` .
			have "meets a b C D" using meet_b[OF `axioms` `a \<noteq> b` `C \<noteq> D` `col a b d` `col C D d`] .
			have "\<not> (meets a b C D)" using `\<not> (meets a b C D)` .
			show "False" using `\<not> (meets a b C D)` `meets a b C D` by blast
		qed
		hence "d \<noteq> P" by blast
		have "col P b a" using collinear4[OF `axioms` `col d P b` `col d P a` `d \<noteq> P`] .
		have "col P b c" using collinear_b `axioms` `bet P b c` by blast
		have "b \<noteq> P" using betweennotequal[OF `axioms` `bet c b P`] by blast
		have "P \<noteq> b" using inequalitysymmetric[OF `axioms` `b \<noteq> P`] .
		have "col b a c" using collinear4[OF `axioms` `col P b a` `col P b c` `P \<noteq> b`] .
		have "col b a c" using `col b a c` .
		have "col a b c" using collinearorder[OF `axioms` `col b a c`] by blast
		have "meets a b C D" using meet_b[OF `axioms` `a \<noteq> b` `C \<noteq> D` `col a b c` `col C D c`] .
		have "\<not> (meets a b C D)" using `\<not> (meets a b C D)` .
		show "False" using `\<not> (meets a b C D)` `meets a b C D` by blast
	qed
	hence "\<not> col a d P" by blast
	obtain M where "bet P M d \<and> bet a b M" using Pasch_outerE[OF `axioms` `bet P b e` `bet a e d` `\<not> col a d P`]  by  blast
	have "bet P M d" using `bet P M d \<and> bet a b M` by blast
	have "bet a b M" using `bet P M d \<and> bet a b M` by blast
	have "bet P b c" using betweennesssymmetryE[OF `axioms` `bet c b P`] .
	have "col a b M" using collinear_b `axioms` `bet P M d \<and> bet a b M` by blast
	have "col A B a" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a e d \<and> bet c e b` by blast
	have "col A B b" using `col A B b` .
	have "col B a b" using collinear4[OF `axioms` `col A B a` `col A B b` `A \<noteq> B`] .
	have "col b a B" using collinearorder[OF `axioms` `col B a b`] by blast
	have "col b a M" using collinearorder[OF `axioms` `col a b M`] by blast
	have "b \<noteq> a" using inequalitysymmetric[OF `axioms` `a \<noteq> b`] .
	have "col a B M" using collinear4[OF `axioms` `col b a B` `col b a M` `b \<noteq> a`] .
	have "col a B A" using collinearorder[OF `axioms` `col A B a`] by blast
	consider "a \<noteq> B"|"a = B" by blast
	hence "col A B M"
	proof (cases)
		assume "a \<noteq> B"
		have "col B M A" using collinear4[OF `axioms` `col a B M` `col a B A` `a \<noteq> B`] .
		have "col A B M" using collinearorder[OF `axioms` `col B M A`] by blast
		thus ?thesis by blast
	next
		assume "a = B"
		have "A \<noteq> a" using `A \<noteq> B` `a = B` by blast
		have "col A a b" using `col A B b` `a = B` by blast
		have "col b a A" using collinearorder[OF `axioms` `col A a b`] by blast
		have "col b a M" using `col b a M` .
		have "col a A M" using collinear4[OF `axioms` `col b a A` `col b a M` `b \<noteq> a`] .
		have "col a A B" using collinearorder[OF `axioms` `col A B a`] by blast
		have "a \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> a`] .
		have "col A M B" using collinear4[OF `axioms` `col a A M` `col a A B` `a \<noteq> A`] .
		have "col A B M" using collinearorder[OF `axioms` `col A M B`] by blast
		thus ?thesis by blast
	qed
	have "bet c b P" using betweennesssymmetryE[OF `axioms` `bet P b c`] .
	have "bet d M P" using betweennesssymmetryE[OF `axioms` `bet P M d`] .
	have "\<not> (col A B c)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col A B c))"
hence "col A B c" by blast
		have "meets A B C D" using meet_b[OF `axioms` `A \<noteq> B` `C \<noteq> D` `col A B c` `col C D c`] .
		show "False" using `meets A B C D` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a e d \<and> bet c e b` by blast
	qed
	hence "\<not> col A B c" by blast
	have "\<not> (col A B d)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col A B d))"
hence "col A B d" by blast
		have "meets A B C D" using meet_b[OF `axioms` `A \<noteq> B` `C \<noteq> D` `col A B d` `col C D d`] .
		show "False" using `meets A B C D` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a e d \<and> bet c e b` by blast
	qed
	hence "\<not> col A B d" by blast
	have "col A B b \<and> col A B M \<and> bet c b P \<and> bet d M P \<and> \<not> col A B c \<and> \<not> col A B d" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a e d \<and> bet c e b` `col A B M` `bet c b P` `bet d M P` `\<not> col A B c` `\<not> col A B d` by blast
	have "same_side c d A B" using sameside_b[OF `axioms` `col A B b` `col A B M` `bet c b P` `bet d M P` `\<not> col A B c` `\<not> col A B d`] .
	have "\<not> (meets A B c d)"
	proof (rule ccontr)
		assume "\<not> (\<not> (meets A B c d))"
hence "meets A B c d" by blast
		obtain R where "A \<noteq> B \<and> c \<noteq> d \<and> col A B R \<and> col c d R" using meet_f[OF `axioms` `meets A B c d`]  by  blast
		have "col A B R" using `A \<noteq> B \<and> c \<noteq> d \<and> col A B R \<and> col c d R` by blast
		have "col C D c" using `col C D c` .
		have "col C D d" using `col C D d` .
		have "col D c d" using collinear4[OF `axioms` `col C D c` `col C D d` `C \<noteq> D`] .
		have "col D C c" using collinearorder[OF `axioms` `col C D c`] by blast
		have "col D C d" using collinearorder[OF `axioms` `col C D d`] by blast
		have "D \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> D`] .
		have "col C c d" using collinear4[OF `axioms` `col D C c` `col D C d` `D \<noteq> C`] .
		have "col c d C" using collinearorder[OF `axioms` `col C c d`] by blast
		have "col c d D" using collinearorder[OF `axioms` `col D c d`] by blast
		have "col c d R" using `A \<noteq> B \<and> c \<noteq> d \<and> col A B R \<and> col c d R` by blast
		have "col C D R" using collinear5[OF `axioms` `c \<noteq> d` `col c d C` `col c d D` `col c d R`] .
		have "meets A B C D" using meet_b[OF `axioms` `A \<noteq> B` `C \<noteq> D` `col A B R` `col C D R`] .
		have "\<not> (meets A B C D)" using `\<not> (meets A B C D)` .
		show "False" using `\<not> (meets A B C D)` `meets A B C D` by blast
	qed
	hence "\<not> (meets A B c d)" by blast
	have "A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a e d \<and> bet c e b` `A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D c \<and> col C D d \<and> c \<noteq> d \<and> \<not> (meets A B C D) \<and> bet a e d \<and> bet c e b` `\<not> (meets A B c d)` `same_side c d A B` by blast
	have "tarski_parallel A B c d" using tarski_parallel_b[OF `axioms` `A \<noteq> B` `c \<noteq> d` `\<not> (meets A B c d)` `same_side c d A B`] .
	have "col C D c" using `col C D c` .
	have "col C D d" using `col C D d` .
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "col C D C" using collinear_b `axioms` `C = C` by blast
	have "col c d C" using collinear5[OF `axioms` `C \<noteq> D` `col C D c` `col C D d` `col C D C`] .
	have "\<not> (\<not> (tarski_parallel A B C D))"
	proof (rule ccontr)
		assume "\<not> (\<not> (\<not> (tarski_parallel A B C D)))"
hence "\<not> (tarski_parallel A B C D)" by blast
		have "D \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> D`] .
		have "\<not> (C \<noteq> d)"
		proof (rule ccontr)
			assume "\<not> (\<not> (C \<noteq> d))"
hence "C \<noteq> d" by blast
			have "tarski_parallel A B C d" using parallelcollinear[OF `axioms` `tarski_parallel A B c d` `col c d C` `C \<noteq> d`] .
			have "tarski_parallel A B d C" using tarskiparallelflip[OF `axioms` `tarski_parallel A B C d`] by blast
			have "col d C D" using collinearorder[OF `axioms` `col C D d`] by blast
			have "tarski_parallel A B D C" using parallelcollinear[OF `axioms` `tarski_parallel A B d C` `col d C D` `D \<noteq> C`] .
			have "tarski_parallel A B C D" using tarskiparallelflip[OF `axioms` `tarski_parallel A B D C`] by blast
			show "False" using `tarski_parallel A B C D` `\<not> (tarski_parallel A B C D)` by blast
		qed
		hence "C = d" by blast
		have "tarski_parallel A B c C" using `tarski_parallel A B c d` `C = d` by blast
		have "col c C D" using collinearorder[OF `axioms` `col C D c`] by blast
		have "tarski_parallel A B D C" using parallelcollinear[OF `axioms` `tarski_parallel A B c C` `col c C D` `D \<noteq> C`] .
		have "tarski_parallel A B C D" using tarskiparallelflip[OF `axioms` `tarski_parallel A B D C`] by blast
		show "False" using `tarski_parallel A B C D` `\<not> (tarski_parallel A B C D)` by blast
	qed
	hence "tarski_parallel A B C D" by blast
	thus ?thesis by blast
qed

end