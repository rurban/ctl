#!/usr/bin/perl
use GD::Graph::lines;
use GD::Graph::colour 'add_colour';

sub lines_from_file {
  return \@lines;
}

sub plot_data_from_file {
  my $log_fname = shift;
  my $name_plot_hash = {};
  open my $fh, "<", $log_fname or die;
  my $plot_name;
  while (<$fh>) {
    if (/\./) {
      $plot_name = $_;
      $name_plot_hash->{$plot_name} = {
        "num_of_ints" => [],
        "time" => []
      }
    }
    elsif (/(\d+)\s+(\d+)/) {
      my ($x, $y) = ($1, $2);
      push @{$name_plot_hash->{$plot_name}->{num_of_ints}}, $x;
      push @{$name_plot_hash->{$plot_name}->{time}}, $y / 1e6;
    }
  }
  return $name_plot_hash;                     
}

sub plot_from_data {
  my ($graph, $plot, $title) = @_;
  my $color_for_c = 'dgray';
  my $color_for_cc = 'lgray';
  add_colour ($color_for_c, '#333');
  add_colour ($color_for_cc, '#888');
  add_colour ('gridclr', '#C9C9C9');
  add_colour ('plot_bg', '#F9F9F9');
  add_colour ('paper_bg', '#F6F8FA');
  add_colour ('clr1', '#003f5c');
  add_colour ('clr2', '#444e86');
  add_colour ('clr3', '#955196');
  add_colour ('clr4', '#dd5182');
  add_colour ('clr5', '#ff6e54');
  add_colour ('clr6', '#ffa600');
  my $color_list = [ qw(clr1 clr2 clr3 clr4 clr5 clr6)];
  $graph->set(
    x_label => 'Size',
    y_label => 'Seconds',
    title => $title,
    transparent => 0,
    bgclr => '#F9F9F9',
    );
  my (@legend, @linestypes, @data);
  for (keys %{$plot}) {
    my $x = $plot->{$_}->{num_of_ints};
    my $y = $plot->{$_}->{time};
    if (/\.cc$/) {
      push @linestypes, 3; # dot
      push @colors, $color_for_cc;
    } else {
      push @linestypes, 1; # solid
      push @colors, $color_for_c;
    }
    push @data, $y;
    push @legend, $_;
  }
  $graph->set(line_types => \@linestypes,
              dclrs => \@colors);
  $graph->set_legend(@legend);
  return $graph->plot(\@data);
  #$used_basenames = []
  #$trace_list = []
  #for idx, name in enumerate(name_plot_hash.keys()):
  #    trace_color = color_list[int(idx / 2)]
  #    trace = go.Scatter(
  #        x=name_plot_hash[name]["num_of_ints"],
  #        y=name_plot_hash[name]["time"],
  #        name=name,
  #        mode="lines",
  #        marker=dict(color=trace_color),
  #        line=dict(width=2, dash=("dot" if name.endswith(".cc") else "solid"))
  #    )
  #    trace_list.append(trace)
  #fig = go.Figure(data=trace_list)
  #fig.update_layout(
  #    plot_bgcolor=plot_bgcolor,
  #    paper_bgcolor=paper_bgcolor,
  #    xaxis=dict(title="Size", nticks=40, showgrid=True, gridcolor=grid_color),
  #    yaxis=dict(title="Seconds", showgrid=True, gridcolor=grid_color, type="log"),
  #    title=title
  #)
}

my $filename = shift;
my $title = shift;
my $name_plot = plot_data_from_file ($filename);
my $graph = GD::Graph::lines->new(1000, 500);
my $gd = plot_from_data ($graph, $name_plot, $title);

open my $img, ">", "$filename.png" or die;
print $img $gd->png;
close $img;
