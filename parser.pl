#!/usr/bin/perl -w
package parser;

sub readFile {
    my @R;
    my ($input_file,$type) = @_; 
    my $nof_nodes = 0;
    my $nof_edges = 0;
    open(IN, "<$input_file") || die "$0: $! $input_file";

    if ($type) {
	while (<IN>){
	    # ���Ԥ򥹥��åפ���
	    if(/^\s*$/) { next; }
	    # ʸ��������Ԥ�̵�뤹��
	    if(/[a-z]+/) { next; }
	    # �Ρ��ɿ��Τߤ򵭺ܤ��Ƥ���Ԥ�̵�뤹��
	    if(/^\d+$/) { next; }

	    # ���å��Ԥ�ѡ�������
	    my @nodes = split;
	    for (my $i=2; $i<@nodes; $i++) {
		${$R[$nodes[0]+1]}{$nodes[$i]+1} = 1;
		my $n1 = $nodes[0]+1;
		my $n2 = $nodes[$i]+1;
		print "$n1,$n2\n";
	    }
	}
    } else {
	##�ե����뤫��ȿ�����ɤ߹���
	while (<IN>){
	    # ���Ԥ򥹥��åפ���
	    if(/^\s*$/){  next; }
	    # �Ρ��ɿ��ȥ��å������l������
	    if(/^p\s+edge[s]*\s+(\d+?)\s+(\d+?)\s*$/){
		$nof_nodes = $1;
		$nof_edges = $2;
	    }
	    # ���å��Ԥ�ѡ������� (�������˥��å�����Ͽ����)
	    if(/^e\s+(\d+?)\s+(\d+?)\s*$/){
		my ($n1,$n2) = ($1,$2);
		if ($n1==$n2) { 
#		    print "selfedge\n"; 
		    next; 
		} #��ʬ���ȤؤΥ��å����Ե���
		${$R[$n1]}{$n2} = 1;
		${$R[$n2]}{$n1} = 1;
		next;
	    }
	}
    }

    my $deg1Flag=0;
    my $noeFlag=0;
    my %old2new = (); # �Ť��ֹ椫�鿷�����ֹ�ؤμ���
    my $new_node_index=1;
    my @G=();
    my $edge_sum=0;

    for (my $i=1; $i <= $nof_nodes; $i++) {
	#�Ρ����������Ǥ�¸�ߤ����
    	if ($R[$i]) { 
	    $old2new{$i} = $new_node_index;
	    $new_node_index++;
    	    my $nof_neighbor = keys %{$R[$i]};
	    $edge_sum += $nof_neighbor;
	    if ($nof_neighbor < 2) {
    	 	$deg1Flag=1;
	    }
   	} else {
	    $noeFlag=1;
    	}
    }

    # �Ρ����ֹ椬�ͤޤäƤ��ʤ�����դϺƹ������Ƶͤ��
    # ���κ�Ȥˤ���Υե�����ȥΡ����ֹ�ϰ��פ��ʤ��ʤ�
    if ($noeFlag) {
#	print "reconstruct\n";
	for (my $i=1; $i <= $nof_nodes; $i++) {
	    foreach my $j (keys %{$R[$i]}) {
		${$G[$old2new{$i}]}{$old2new{$j}} = 1 ;
		${$G[$old2new{$j}]}{$old2new{$i}} = 1 ;
#		print "test\n";
	    }
	}

	if ($edge_sum % 2) {
	    print "graph reconstruction error -- abort\n";
	    exit ();
	}
	
	$nof_nodes = $new_node_index - 1;
	$nof_edges = $edge_sum / 2;

	# for (my $i=1; $i<@G; $i++) {
	#     my $deg = keys %{$G[$i]};
	#     if ($deg < 3) {
	# 	print "deg($i)=$deg\n";
	#     }
	# }
	
	return (\@G, $nof_nodes, $nof_edges, $deg1Flag);
    }

    # for (my $i=1; $i<@R; $i++) {
    # 	my $deg = keys %{$R[$i]};
    # 	if ($deg < 1000) {
    # 	    print "deg($i)=$deg\n";
    # 	}
    # }

return (\@R, $nof_nodes, $nof_edges, $deg1Flag);
    

}#END OF "read_file"

1;
