theory parallelcollinear2
	imports Axioms Definitions Theorems
begin

theorem parallelcollinear2:
	assumes: `axioms`
		"tarski_parallel A B c d"
		"bet c C d"
	shows: "tarski_parallel A B C d"
proof -
	have "A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B" using tarski_parallel_f[OF `axioms` `tarski_parallel A B c d`] .
	have "A \<noteq> B" using `A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B` by blast
	have "c \<noteq> d" using `A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B` by blast
	have "same_side c d A B" using `A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B` by blast
	obtain p q r where "col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d" using sameside_f[OF `axioms` `same_side c d A B`] by blast
	have "col A B p" using `col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d` by blast
	have "col A B r" using `col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d` by blast
	have "bet c p q" using `col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d` by blast
	have "bet d r q" using `col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d` by blast
	have "C \<noteq> d" using betweennotequal[OF `axioms` `bet c C d`] by blast
	have "bet q r d" using betweennesssymmetryE[OF `axioms` `bet d r q`] .
	have "bet d C c" using betweennesssymmetryE[OF `axioms` `bet c C d`] .
	have "bet q p c" using betweennesssymmetryE[OF `axioms` `bet c p q`] .
	have "col q p c" using collinear_b `axioms` `bet q p c` by blast
	have "\<not> (p = r)"
	proof (rule ccontr)
		assume "p = r"
		have "col q r d" using collinear_b `axioms` `bet q r d` by blast
		have "col q p c" using collinear_b `axioms` `bet q p c` by blast
		have "col q p d" using `col q r d` `p = r` by blast
		have "q \<noteq> p" using betweennotequal[OF `axioms` `bet q p c`] by blast
		have "col p c d" using collinear4[OF `axioms` `col q p c` `col q p d` `q \<noteq> p`] .
		have "col c d p" using collinearorder[OF `axioms` `col p c d`] by blast
		have "meets A B c d" using meet_b[OF `axioms` `A \<noteq> B` `c \<noteq> d` `col A B p` `col c d p`] .
		have "\<not> (meets A B c d)" using `A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B` by blast
		show "False" using `\<not> (meets A B c d)` `meets A B c d` by blast
	qed
	hence "p \<noteq> r" by blast
	have "\<not> col A B c" using `col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d` by blast
	have "\<not> col A B d" using `col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d` by blast
	have "\<not> col p r c" using NChelper[OF `axioms` `\<not> col A B c` `col A B p` `col A B r` `p \<noteq> r`] .
	have "\<not> col p r d" using NChelper[OF `axioms` `\<not> col A B d` `col A B p` `col A B r` `p \<noteq> r`] .
	have "\<not> col r d p" using NCorder[OF `axioms` `\<not> col p r d`] by blast
	have "col q r d" using collinear_b `axioms` `bet q r d` by blast
	have "col r d q" using collinearorder[OF `axioms` `col q r d`] by blast
	have "d = d" using equalityreflexiveE[OF `axioms`] .
	have "col r d d" using collinear_b `axioms` `d = d` by blast
	have "q \<noteq> d" using betweennotequal[OF `axioms` `bet q r d`] by blast
	have "\<not> col q d p" using NChelper[OF `axioms` `\<not> col r d p` `col r d q` `col r d d` `q \<noteq> d`] .
	have "\<not> col q p d" using NCorder[OF `axioms` `\<not> col q d p`] by blast
	have "\<not> (c = p)"
	proof (rule ccontr)
		assume "c = p"
		have "p = c" using equalitysymmetric[OF `axioms` `c = p`] .
		have "col p r c" using collinear_b `axioms` `p = c` by blast
		have "\<not> col p r c" using `\<not> col p r c` .
		show "False" using `\<not> col p r c` `col p r c` by blast
	qed
	hence "c \<noteq> p" by blast
	have "col q p c" using `col q p c` .
	have "p = p" using equalityreflexiveE[OF `axioms`] .
	have "col q p p" using collinear_b `axioms` `p = p` by blast
	have "\<not> col c p d" using NChelper[OF `axioms` `\<not> col q p d` `col q p c` `col q p p` `c \<noteq> p`] .
	have "col c p q" using collinearorder[OF `axioms` `col q p c`] by blast
	have "c = c" using equalityreflexiveE[OF `axioms`] .
	have "col c p c" using collinear_b `axioms` `c = c` by blast
	have "q \<noteq> c" using betweennotequal[OF `axioms` `bet q p c`] by blast
	have "\<not> col q c d" using NChelper[OF `axioms` `\<not> col c p d` `col c p q` `col c p c` `q \<noteq> c`] .
	have "bet q p c" using betweennesssymmetryE[OF `axioms` `bet c p q`] .
	obtain E where "bet q E C \<and> bet d E p" using Pasch-innerE[OF `axioms` `bet q p c` `bet d C c` `\<not> col q c d`] by blast
	have "bet d E p" using `bet q E C \<and> bet d E p` by blast
	have "bet p E d" using betweennesssymmetryE[OF `axioms` `bet d E p`] .
	have "bet q r d" using betweennesssymmetryE[OF `axioms` `bet d r q`] .
	have "\<not> col q d p" using `\<not> col q d p` .
	obtain F where "bet q F E \<and> bet p F r" using Pasch-innerE[OF `axioms` `bet q r d` `bet p E d` `\<not> col q d p`] by blast
	have "bet p F r" using `bet q F E \<and> bet p F r` by blast
	have "col p r F" using collinear_b `axioms` `bet q F E \<and> bet p F r` by blast
	have "col B r p" using collinear4[OF `axioms` `col A B r` `col A B p` `A \<noteq> B`] .
	have "col B A p" using collinearorder[OF `axioms` `col A B p`] by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	have "col B p r" using collinearorder[OF `axioms` `col B r p`] by blast
	have "col B p A" using collinearorder[OF `axioms` `col A B p`] by blast
	have "\<not> (col A B C)"
	proof (rule ccontr)
		assume "col A B C"
		have "col c C d" using collinear_b `axioms` `bet c C d` by blast
		have "col c d C" using collinearorder[OF `axioms` `col c C d`] by blast
		have "c \<noteq> d" using `c \<noteq> d` .
		have "A \<noteq> B" using `A \<noteq> B` .
		have "meets A B c d" using meet_b[OF `axioms` `A \<noteq> B` `c \<noteq> d` `col A B C` `col c d C`] .
		have "\<not> (meets A B c d)" using `A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B` by blast
		show "False" using `\<not> (meets A B c d)` `meets A B c d` by blast
	qed
	hence "\<not> col A B C" by blast
	have "bet q E C" using `bet q E C \<and> bet d E p` by blast
	have "bet q F E" using `bet q F E \<and> bet p F r` by blast
	have "bet q F C" using n3_6b[OF `axioms` `bet q F E` `bet q E C`] .
	have "bet C F q" using betweennesssymmetryE[OF `axioms` `bet q F C`] .
	have "bet d r q" using `bet d r q` .
	have "same_side C d A B"
	proof (rule ccontr)
		assume "\<not> (same_side C d A B)"
		have "\<not> (B \<noteq> p)"
		proof (rule ccontr)
			assume "B \<noteq> p"
			have "col p r A" using collinear4[OF `axioms` `col B p r` `col B p A` `B \<noteq> p`] .
			have "col A p r" using collinearorder[OF `axioms` `col p r A`] by blast
			have "col A p B" using collinearorder[OF `axioms` `col A B p`] by blast
			have "bet d r q" using `bet d r q` .
			have "col A B r" using `col A B r` .
			have "\<not> (A \<noteq> p)"
			proof (rule ccontr)
				assume "A \<noteq> p"
				have "col p r B" using collinear4[OF `axioms` `col A p r` `col A p B` `A \<noteq> p`] .
				have "col A B F" using collinear5[OF `axioms` `p \<noteq> r` `col p r A` `col p r B` `col p r F`] .
				have "same_side C d A B" using sameside_b[OF `axioms` `col A B F` `col A B r` `bet C F q` `bet d r q` `\<not> col A B C` `\<not> col A B d`] .
				show "False" using `same_side C d A B` `\<not> (same_side C d A B)` by blast
			qed
			hence "A = p" by blast
			have "col A r F" using `col p r F` `A = p` by blast
			have "col r A F" using collinearorder[OF `axioms` `col A r F`] by blast
			have "col r A B" using collinearorder[OF `axioms` `col A B r`] by blast
			have "\<not> (r = A)"
			proof (rule ccontr)
				assume "r = A"
				have "r = p" using `A = p` `r = A` by blast
				have "p \<noteq> r" using betweennotequal[OF `axioms` `bet p F r`] by blast
				have "r \<noteq> p" using inequalitysymmetric[OF `axioms` `p \<noteq> r`] .
				show "False" using `r \<noteq> p` `r = p` by blast
			qed
			hence "r \<noteq> A" by blast
			have "col A F B" using collinear4[OF `axioms` `col r A F` `col r A B` `r \<noteq> A`] .
			have "col A B F" using collinearorder[OF `axioms` `col A F B`] by blast
			have "same_side C d A B" using sameside_b[OF `axioms` `col A B F` `col A B r` `bet C F q` `bet d r q` `\<not> col A B C` `\<not> col A B d`] .
			show "False" using `same_side C d A B` `\<not> (same_side C d A B)` by blast
		qed
		hence "B = p" by blast
		have "A \<noteq> p" using `A \<noteq> B` `B = p` by blast
		have "A = A" using equalityreflexiveE[OF `axioms`] .
		have "col B A A" using collinear_b `axioms` `A = A` by blast
		have "col B A p" using collinearorder[OF `axioms` `col A B p`] by blast
		have "col B A r" using collinearorder[OF `axioms` `col A B r`] by blast
		have "col A p r" using collinear5[OF `axioms` `B \<noteq> A` `col B A A` `col B A p` `col B A r`] .
		have "col p r B" using collinearorder[OF `axioms` `col B p r`] by blast
		have "col p r A" using collinearorder[OF `axioms` `col A p r`] by blast
		have "col A B F" using collinear5[OF `axioms` `p \<noteq> r` `col p r A` `col p r B` `col p r F`] .
		have "same_side C d A B" using sameside_b[OF `axioms` `col A B F` `col A B r` `bet C F q` `bet d r q` `\<not> col A B C` `\<not> col A B d`] .
		show "False" using `same_side C d A B` `\<not> (same_side C d A B)` by blast
	qed
	hence "same_side C d A B" by blast
	have "\<not> (meets A B C d)"
	proof (rule ccontr)
		assume "meets A B C d"
		obtain R where "A \<noteq> B \<and> C \<noteq> d \<and> col A B R \<and> col C d R" using meet_f[OF `axioms` `meets A B C d`] by blast
		have "col A B R" using `A \<noteq> B \<and> C \<noteq> d \<and> col A B R \<and> col C d R` by blast
		have "col C d R" using `A \<noteq> B \<and> C \<noteq> d \<and> col A B R \<and> col C d R` by blast
		have "col c C d" using collinear_b `axioms` `bet c C d` by blast
		have "col C d c" using collinearorder[OF `axioms` `col c C d`] by blast
		have "C \<noteq> d" using betweennotequal[OF `axioms` `bet c C d`] by blast
		have "col d c R" using collinear4[OF `axioms` `col C d c` `col C d R` `C \<noteq> d`] .
		have "col c d R" using collinearorder[OF `axioms` `col d c R`] by blast
		have "meets A B c d" using meet_b[OF `axioms` `A \<noteq> B` `c \<noteq> d` `col A B R` `col c d R`] .
		have "\<not> (meets A B c d)" using `A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B` by blast
		show "False" using `\<not> (meets A B c d)` `meets A B c d` by blast
	qed
	hence "\<not> (meets A B C d)" by blast
	have "A \<noteq> B \<and> C \<noteq> d \<and> \<not> (meets A B C d) \<and> same_side C d A B" using `A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B` `C \<noteq> d` `\<not> (meets A B C d)` `same_side C d A B` by blast
	have "tarski_parallel A B C d" using tarski_parallel_b[OF `axioms` `A \<noteq> B` `C \<noteq> d` `\<not> (meets A B C d)` `same_side C d A B`] .
	thus ?thesis by blast
qed

end