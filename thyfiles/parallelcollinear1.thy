theory parallelcollinear1
	imports Axioms Definitions Theorems
begin

theorem parallelcollinear1:
	assumes: `axioms`
		"tarski_parallel A B c d"
		"bet C c d"
	shows: "tarski_parallel A B C d"
proof -
	have "C \<noteq> c" using betweennotequal[OF `axioms` `bet C c d`] by blast
	have "c \<noteq> d" using betweennotequal[OF `axioms` `bet C c d`] by blast
	have "C \<noteq> d" using betweennotequal[OF `axioms` `bet C c d`] by blast
	have "A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B" sorry
	have "A \<noteq> B" using `A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B` by blast
	have "c \<noteq> d" using `c \<noteq> d` .
	have "same_side c d A B" using `A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B` by blast
	obtain p q r where "col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d" sorry
	have "col A B p" using `col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d` by blast
	have "col A B r" using `col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d` by blast
	have "bet c p q" using `col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d` by blast
	have "bet d r q" using `col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d` by blast
	have "\<not> col A B c" using `col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d` by blast
	have "\<not> col A B d" using `col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d` by blast
	have "bet q r d" using betweennesssymmetryE[OF `axioms` `bet d r q`] .
	have "col C c d" using col_b `axioms` `bet C c d` by blast
	have "col c d C" using collinearorder[OF `axioms` `col C c d`] by blast
	have "bet d c C" using betweennesssymmetryE[OF `axioms` `bet C c d`] .
	have "bet q r d" using `bet q r d` .
	have "bet q p c" using betweennesssymmetryE[OF `axioms` `bet c p q`] .
	have "\<not> (p = r)"
	proof (rule ccontr)
		assume "p = r"
		have "col q r d" using col_b `axioms` `bet q r d` by blast
		have "col q p c" using col_b `axioms` `bet q p c` by blast
		have "col q p d" sorry
		have "q \<noteq> p" using betweennotequal[OF `axioms` `bet q p c`] by blast
		have "col p c d" using collinear4[OF `axioms` `col q p c` `col q p d` `q \<noteq> p`] .
		have "col c d p" using collinearorder[OF `axioms` `col p c d`] by blast
		have "meets A B c d" sorry
		have "\<not> (meets A B c d)" using `A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B` by blast
		show "False" using `\<not> (meets A B c d)` `meets A B c d` by blast
	qed
	hence "p \<noteq> r" by blast
	have "col q p c" using col_b `axioms` `bet q p c` by blast
	have "\<not> (col q d C)"
	proof (rule ccontr)
		assume "col q d C"
		have "col d c C" using col_b `axioms` `bet d c C` by blast
		have "col C d c" using collinearorder[OF `axioms` `col C c d`] by blast
		have "col C d q" using collinearorder[OF `axioms` `col q d C`] by blast
		have "C \<noteq> d" using betweennotequal[OF `axioms` `bet C c d`] by blast
		have "col d c q" using collinear4[OF `axioms` `col C d c` `col C d q` `C \<noteq> d`] .
		have "col c q d" using collinearorder[OF `axioms` `col d c q`] by blast
		have "col c q p" using collinearorder[OF `axioms` `col q p c`] by blast
		have "q \<noteq> c" using betweennotequal[OF `axioms` `bet q p c`] by blast
		have "c \<noteq> q" using inequalitysymmetric[OF `axioms` `q \<noteq> c`] .
		have "col q d p" using collinear4[OF `axioms` `col c q d` `col c q p` `c \<noteq> q`] .
		have "col q r d" using col_b `axioms` `bet q r d` by blast
		have "col q d r" using collinearorder[OF `axioms` `col q r d`] by blast
		have "q \<noteq> d" using betweennotequal[OF `axioms` `bet q r d`] by blast
		have "col d p r" using collinear4[OF `axioms` `col q d p` `col q d r` `q \<noteq> d`] .
		have "col A B p" using `col A B p` .
		have "col A B r" using `col A B r` .
		have "col B p r" using collinear4[OF `axioms` `col A B p` `col A B r` `A \<noteq> B`] .
		have "col B A p" using collinearorder[OF `axioms` `col A B p`] by blast
		have "col B p A" using collinearorder[OF `axioms` `col A B p`] by blast
		have "col B A r" using collinearorder[OF `axioms` `col A B r`] by blast
		have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
		have "col A p r" using collinear4[OF `axioms` `col B A p` `col B A r` `B \<noteq> A`] .
		have "\<not> (B \<noteq> p)"
		proof (rule ccontr)
			assume "B \<noteq> p"
			have "col p r A" using collinear4[OF `axioms` `col B p r` `col B p A` `B \<noteq> p`] .
			have "col p r d" using collinearorder[OF `axioms` `col d p r`] by blast
			have "col r A d" using collinear4[OF `axioms` `col p r A` `col p r d` `p \<noteq> r`] .
			have "col r A B" using collinearorder[OF `axioms` `col A B r`] by blast
			have "\<not> (r \<noteq> A)"
			proof (rule ccontr)
				assume "r \<noteq> A"
				have "col A d B" using collinear4[OF `axioms` `col r A d` `col r A B` `r \<noteq> A`] .
				have "col A B d" using collinearorder[OF `axioms` `col A d B`] by blast
				have "\<not> col A B d" using `\<not> col A B d` .
				show "False" using `\<not> col A B d` `col A B d` by blast
			qed
			hence "r = A" by blast
			have "col p A d" sorry
			have "col p A B" using collinearorder[OF `axioms` `col A B p`] by blast
			have "\<not> (p \<noteq> A)"
			proof (rule ccontr)
				assume "p \<noteq> A"
				have "col A d B" using collinear4[OF `axioms` `col p A d` `col p A B` `p \<noteq> A`] .
				have "col A B d" using collinearorder[OF `axioms` `col A d B`] by blast
				show "False" using `col A B d` `col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d` by blast
			qed
			hence "p = A" by blast
			have "r = p" using equalitytransitiveE[OF `axioms` `r = A` `p = A`] .
			have "col q p c" using `col q p c` .
			have "col q r d" using `col q r d` .
			have "col q p d" sorry
			have "q \<noteq> p" using betweennotequal[OF `axioms` `bet q p c`] by blast
			have "col p c d" using collinear4[OF `axioms` `col q p c` `col q p d` `q \<noteq> p`] .
			have "col c d p" using collinearorder[OF `axioms` `col p c d`] by blast
			have "meets A B c d" sorry
			have "\<not> (meets A B c d)" using `A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B` by blast
			show "False" using `\<not> (meets A B c d)` `meets A B c d` by blast
		qed
		hence "B = p" by blast
		have "col r A B" using collinearorder[OF `axioms` `col A B r`] by blast
		have "col d B r" sorry
		have "col r B d" using collinearorder[OF `axioms` `col d B r`] by blast
		have "col r B A" using collinearorder[OF `axioms` `col A B r`] by blast
		have "\<not> (r \<noteq> B)"
		proof (rule ccontr)
			assume "r \<noteq> B"
			have "col B d A" using collinear4[OF `axioms` `col r B d` `col r B A` `r \<noteq> B`] .
			have "col A B d" using collinearorder[OF `axioms` `col B d A`] by blast
			show "False" using `col A B d` `col A B p \<and> col A B r \<and> bet c p q \<and> bet d r q \<and> \<not> col A B c \<and> \<not> col A B d` by blast
		qed
		hence "r = B" by blast
		have "p = B" using equalitysymmetric[OF `axioms` `B = p`] .
		have "p = r" using equalitytransitiveE[OF `axioms` `p = B` `r = B`] .
		have "p \<noteq> r" using `p \<noteq> r` .
		show "False" using `p \<noteq> r` `p = r` by blast
	qed
	hence "\<not> col q d C" by blast
	obtain E where "bet q E c \<and> bet C E r" using Pasch-innerE[OF `axioms` `bet q r d` `bet C c d` `\<not> col q d C`]  by  blast
	have "bet q E c" using `bet q E c \<and> bet C E r` by blast
	have "col q E c" using col_b `axioms` `bet q E c \<and> bet C E r` by blast
	have "col q c p" using collinearorder[OF `axioms` `col q p c`] by blast
	have "col q c E" using collinearorder[OF `axioms` `col q E c`] by blast
	have "q \<noteq> c" using betweennotequal[OF `axioms` `bet q E c`] by blast
	have "col c p E" using collinear4[OF `axioms` `col q c p` `col q c E` `q \<noteq> c`] .
	have "r \<noteq> p" using inequalitysymmetric[OF `axioms` `p \<noteq> r`] .
	obtain J where "bet r p J \<and> seg_eq p J r p" using extensionE[OF `axioms` `r \<noteq> p` `r \<noteq> p`]  by  blast
	have "bet r p J" using `bet r p J \<and> seg_eq p J r p` by blast
	have "bet J p r" using betweennesssymmetryE[OF `axioms` `bet r p J`] .
	have "col J p r" using col_b `axioms` `bet J p r` by blast
	have "J \<noteq> r" using betweennotequal[OF `axioms` `bet J p r`] by blast
	have "p \<noteq> r" using betweennotequal[OF `axioms` `bet J p r`] by blast
	have "J \<noteq> p" using betweennotequal[OF `axioms` `bet J p r`] by blast
	have "bet C E r" using `bet q E c \<and> bet C E r` by blast
	have "col A B p" using `col A B p` .
	have "col A B r" using `col A B r` .
	have "col B p r" using collinear4[OF `axioms` `col A B p` `col A B r` `A \<noteq> B`] .
	have "col B A p" using collinearorder[OF `axioms` `col A B p`] by blast
	have "col B A r" using collinearorder[OF `axioms` `col A B r`] by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	have "col A p r" using collinear4[OF `axioms` `col B A p` `col B A r` `B \<noteq> A`] .
	have "col p r A" using collinearorder[OF `axioms` `col A p r`] by blast
	have "col p r B" using collinearorder[OF `axioms` `col B p r`] by blast
	have "\<not> (meets C d J r)"
	proof (rule ccontr)
		assume "meets C d J r"
		obtain K where "C \<noteq> d \<and> J \<noteq> r \<and> col C d K \<and> col J r K" sorry
		have "C \<noteq> d" using `C \<noteq> d` .
		have "J \<noteq> r" using `J \<noteq> r` .
		have "col C d K" using `C \<noteq> d \<and> J \<noteq> r \<and> col C d K \<and> col J r K` by blast
		have "col J r K" using `C \<noteq> d \<and> J \<noteq> r \<and> col C d K \<and> col J r K` by blast
		have "col C c d" using col_b `axioms` `bet C c d` by blast
		have "col C d c" using collinearorder[OF `axioms` `col C c d`] by blast
		have "c \<noteq> d" using betweennotequal[OF `axioms` `bet C c d`] by blast
		have "d \<noteq> c" using inequalitysymmetric[OF `axioms` `c \<noteq> d`] .
		have "col d c K" using collinear4[OF `axioms` `col C d c` `col C d K` `C \<noteq> d`] .
		have "col c d K" using collinearorder[OF `axioms` `col d c K`] by blast
		have "col r J p" using collinearorder[OF `axioms` `col J p r`] by blast
		have "r \<noteq> J" using betweennotequal[OF `axioms` `bet r p J`] by blast
		have "col r J K" using collinearorder[OF `axioms` `col J r K`] by blast
		have "col J p K" using collinear4[OF `axioms` `col r J p` `col r J K` `r \<noteq> J`] .
		have "col J p r" using collinearorder[OF `axioms` `col r J p`] by blast
		have "p \<noteq> J" using betweennotequal[OF `axioms` `bet r p J`] by blast
		have "J \<noteq> p" using inequalitysymmetric[OF `axioms` `p \<noteq> J`] .
		have "col p K r" using collinear4[OF `axioms` `col J p K` `col J p r` `J \<noteq> p`] .
		have "col p r K" using collinearorder[OF `axioms` `col p K r`] by blast
		have "col p r A" using `col p r A` .
		have "col p r B" using `col p r B` .
		have "col A B K" using collinear5[OF `axioms` `p \<noteq> r` `col p r A` `col p r B` `col p r K`] .
		have "meets A B c d" sorry
		have "\<not> (meets A B c d)" using `A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B` by blast
		show "False" using `\<not> (meets A B c d)` `meets A B c d` by blast
	qed
	hence "\<not> (meets C d J r)" by blast
	have "bet c E p" using collinearbetween[OF `axioms` `col C c d` `col J p r` `C \<noteq> d` `J \<noteq> r` `C \<noteq> c` `p \<noteq> r` `\<not> (meets C d J r)` `bet C E r` `col c p E`] .
	have "bet p E c" using betweennesssymmetryE[OF `axioms` `bet c E p`] .
	have "bet q p E" using innertransitivityE[OF `axioms` `bet q p c` `bet p E c`] .
	have "p \<noteq> r" using `p \<noteq> r` .
	have "\<not> col p r c" using NChelper[OF `axioms` `\<not> col A B c` `col A B p` `col A B r` `p \<noteq> r`] .
	have "\<not> col p c r" using NCorder[OF `axioms` `\<not> col p r c`] by blast
	have "col q p c" using col_b `axioms` `bet q p c` by blast
	have "col p c q" using collinearorder[OF `axioms` `col q c p`] by blast
	have "c = c" using equalityreflexiveE[OF `axioms`] .
	have "col p c c" using col_b `axioms` `c = c` by blast
	have "q \<noteq> c" using betweennotequal[OF `axioms` `bet q E c`] by blast
	have "\<not> col q c r" using NChelper[OF `axioms` `\<not> col p c r` `col p c q` `col p c c` `q \<noteq> c`] .
	have "\<not> col q r c" using NCorder[OF `axioms` `\<not> col q c r`] by blast
	have "q \<noteq> d" using betweennotequal[OF `axioms` `bet q r d`] by blast
	have "q = q" using equalityreflexiveE[OF `axioms`] .
	have "col d c C" using collinearorder[OF `axioms` `col C c d`] by blast
	have "C \<noteq> d" using betweennotequal[OF `axioms` `bet C c d`] by blast
	have "d \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> d`] .
	have "\<not> col d q C" using NCorder[OF `axioms` `\<not> col q d C`] by blast
	have "col q r d" using col_b `axioms` `bet q r d` by blast
	have "col d q r" using collinearorder[OF `axioms` `col q r d`] by blast
	have "col d q q" using col_b `axioms` `q = q` by blast
	have "\<not> (r = C)"
	proof (rule ccontr)
		assume "r = C"
		have "col c d C" using `col c d C` .
		have "col A B r" using `col A B r` .
		have "col A B C" sorry
		have "meets A B c d" sorry
		have "\<not> (meets A B c d)" using `A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B` by blast
		show "False" using `\<not> (meets A B c d)` `meets A B c d` by blast
	qed
	hence "r \<noteq> C" by blast
	have "\<not> (r = q)"
	proof (rule ccontr)
		assume "r = q"
		have "col r q c" using col_b `axioms` `r = q` by blast
		have "col q r c" using collinearorder[OF `axioms` `col r q c`] by blast
		show "False" using `col q r c` `\<not> col q r c` by blast
	qed
	hence "r \<noteq> q" by blast
	have "\<not> col r q C" using NChelper[OF `axioms` `\<not> col d q C` `col d q r` `col d q q` `r \<noteq> q`] .
	have "\<not> col r C q" using NCorder[OF `axioms` `\<not> col r q C`] by blast
	have "bet r E C" using betweennesssymmetryE[OF `axioms` `bet C E r`] .
	have "bet q p E" using `bet q p E` .
	obtain F where "bet q F C \<and> bet r p F" using Pasch-outerE[OF `axioms` `bet q p E` `bet r E C` `\<not> col r C q`]  by  blast
	have "bet q F C" using `bet q F C \<and> bet r p F` by blast
	have "bet C F q" using betweennesssymmetryE[OF `axioms` `bet q F C`] .
	have "bet r p F" using `bet q F C \<and> bet r p F` by blast
	have "col r p F" using col_b `axioms` `bet q F C \<and> bet r p F` by blast
	have "col r p A" using collinearorder[OF `axioms` `col A p r`] by blast
	have "col r p B" using collinearorder[OF `axioms` `col B p r`] by blast
	have "col A B F" using collinear5[OF `axioms` `r \<noteq> p` `col r p A` `col r p B` `col r p F`] .
	have "\<not> col q C r" using NCorder[OF `axioms` `\<not> col r C q`] by blast
	have "col q F C" using col_b `axioms` `bet q F C \<and> bet r p F` by blast
	have "col q C F" using collinearorder[OF `axioms` `col q F C`] by blast
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "col q C C" using col_b `axioms` `C = C` by blast
	have "F \<noteq> C" using betweennotequal[OF `axioms` `bet q F C`] by blast
	have "\<not> col F C r" using NChelper[OF `axioms` `\<not> col q C r` `col q C F` `col q C C` `F \<noteq> C`] .
	have "\<not> col F r C" using NCorder[OF `axioms` `\<not> col F C r`] by blast
	have "col A B r" using `col A B r` .
	have "col A B p" using `col A B p` .
	have "col p r A" using collinearorder[OF `axioms` `col A p r`] by blast
	have "col p r F" using collinearorder[OF `axioms` `col r p F`] by blast
	have "p \<noteq> r" using betweennotequal[OF `axioms` `bet J p r`] by blast
	have "col r A F" using collinear4[OF `axioms` `col p r A` `col p r F` `p \<noteq> r`] .
	have "col F r A" using collinearorder[OF `axioms` `col r A F`] by blast
	have "col B A r" using collinearorder[OF `axioms` `col A B r`] by blast
	have "col B A p" using collinearorder[OF `axioms` `col A B p`] by blast
	have "col A B r" using collinearorder[OF `axioms` `col B A r`] by blast
	have "col A B p" using collinearorder[OF `axioms` `col B A p`] by blast
	have "col p r B" using collinearorder[OF `axioms` `col B p r`] by blast
	have "col r B F" using collinear4[OF `axioms` `col p r B` `col p r F` `p \<noteq> r`] .
	have "col F r B" using collinearorder[OF `axioms` `col r B F`] by blast
	have "\<not> col A B C" using NChelper[OF `axioms` `\<not> col F r C` `col F r A` `col F r B` `A \<noteq> B`] .
	have "same_side C d A B" sorry
	have "\<not> (meets A B C d)"
	proof (rule ccontr)
		assume "meets A B C d"
		obtain K where "A \<noteq> B \<and> C \<noteq> d \<and> col A B K \<and> col C d K" sorry
		have "A \<noteq> B" using `A \<noteq> B` .
		have "col A B K" using `A \<noteq> B \<and> C \<noteq> d \<and> col A B K \<and> col C d K` by blast
		have "col C d K" using `A \<noteq> B \<and> C \<noteq> d \<and> col A B K \<and> col C d K` by blast
		have "col C d c" using collinearorder[OF `axioms` `col C c d`] by blast
		have "C \<noteq> d" using betweennotequal[OF `axioms` `bet C c d`] by blast
		have "col d c K" using collinear4[OF `axioms` `col C d c` `col C d K` `C \<noteq> d`] .
		have "col c d K" using collinearorder[OF `axioms` `col d c K`] by blast
		have "meets A B c d" sorry
		have "\<not> (meets A B c d)" using `A \<noteq> B \<and> c \<noteq> d \<and> \<not> (meets A B c d) \<and> same_side c d A B` by blast
		show "False" using `\<not> (meets A B c d)` `meets A B c d` by blast
	qed
	hence "\<not> (meets A B C d)" by blast
	have "C \<noteq> d" using betweennotequal[OF `axioms` `bet C c d`] by blast
	have "tarski_parallel A B C d" sorry
	thus ?thesis by blast
qed

end