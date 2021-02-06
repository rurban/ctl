#!/usr/bin/perl
# update the grid from the sorted list in README.md and
# crosscheck with the tests if it is stable (x), not yet implemented () or still
# broken (.).

use strict;
#use Algorithm::Diff qw(diff);

open my $in, '<', 'README.md' or die "$! README.md";
my @c = qw(vec str arr deq list set map uset umap pqu que stk);
my %long = (
  vec => 'vector',
  str => 'string',
  arr => 'array',
  deq => 'deque',
  list => 'list',
  set => 'set',
  map => 'map',
  uset => 'unordered_set',
  umap => 'unordered_map',
  pqu => 'priority_queue',
  que => 'queue',
  stk => 'stack',
);
my $m = {};
my ($found, @m, @l, %seen);
while (<$in>) {
  if (/^\+----+\+/) {
    $found++; next;
  }
  next if /^\s+vec/;
  $found = 0 if /^```/;
  $found = 0 if /^## /;
  if ($found and /^(\w+)/) {
    push @m, $1;
    push @l, $_; # for diff
    $m->{$1} = {};
  }
}
close $in;

# check all tests for its status
sub status {
  my ($c,$f) = @_;
  open my $in, '<', $f or die "$! $f";
  my ($status);
  while (<$in>) {
    if (/^#define FOREACH_METH/) {
      $status = 'x';
    }
    elsif (/^#define FOREACH_DEBUG/) {
      $status = '.';
    }
    #elsif (/^#define GENERATE_ENUM/) {
    #  close $in;
    #  return;
    #}
    elsif (/^\s+TEST\((\w+)\)/) {
      next if $1 eq 'SELF';
      $m->{$c}->{lc $1} = $status;
    }
    elsif (/^\s+case TEST_(\w+):/) {
      $seen{lc $1}++;
    }
  }
  close $in;
  foreach (keys %{$m->{$c}}) {
    # check if the test case is defined or not
    next if $m->{$c}->{$_} eq 'x';
    if (!exists $seen{$_}) {
      #warn "$c.$_ unhandled\n";
      delete $m->{$c}->{$_};
    }
  }
}

for (keys %long) {
  my $f = "tests/func/test_" . $long{$_} . ".cc";
  die "no $f $!" unless -e $f;
  status($_,$f);
}

# add common methods, untested per se
for my $c (@c) {
  for (qw(init init_from free equal size max_size empty)) {
    $m->{$c}->{$_} = 'x';
  }
}
for my $c (qw(vec str arr deq list set map uset umap)) {
  for (qw(begin end next foreach)) {
    $m->{$c}->{$_} = 'x';
  }
}
for my $c (qw(vec str arr deq list set map)) {
  for (qw(advance distance ref range foreach_range foreach_n foreach_n_range)) {
    $m->{$c}->{$_} = 'x';
  }
}
for my $c (qw(uset umap)) {
  for (qw(load_factor max_load_factor max_bucket_count bucket_size)) {
    $m->{$c}->{$_} = 'x';
  }
}

# layout:
#   5 space for the col
my $M = 31; # longest method name

sub line {
  # 30 + 5x @c
  my $x = $M + 5 * @c - 3;
  printf "+%s+\n", '-' x $x;
}
sub hdr {
  printf "%-${M}s", '';
  printf "%-5s", $_ for @c;
  printf "\n";
}

# print grid
hdr();
line();
for (@m) {
  printf "%-${M}s", $_;
  # sort methods in $m->{$c} by order in @c
  for my $c (@c) {
    printf "%-5s", $m->{$c}->{$_};
  }
  printf "\n";
  if (/^(key_compare|range)$/) {
    line();
    hdr();
    line();
  }
}
line();
hdr();

#close $out;
#if (system "diff $outfn $outfn.tmp") {
#  system "mv $outfn.tmp $outfn";
#} else {
#  system "rm $outfn.tmp";
#}

