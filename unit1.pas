//Copyright 2020 Andrey S. Ionisyan (anserion@gmail.com)
//
//Licensed under the Apache License, Version 2.0 (the "License");
//you may not use this file except in compliance with the License.
//You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
//Unless required by applicable law or agreed to in writing, software
//distributed under the License is distributed on an "AS IS" BASIS,
//WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//See the License for the specific language governing permissions and
//limitations under the License.

//программа синтеза изображений двумерных волн
//и спектральная обработка (Фурье-анализ-синтез)
unit Unit1;

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, FileUtil, Forms, Controls, Graphics, Dialogs, ExtCtrls,
  StdCtrls, Grids, Buttons, ComCtrls;

type

  { TForm1 }

  TForm1 = class(TForm)
    Bevel1: TBevel;
    BTN_signal_xy_random: TButton;
    BTN_signal_xy_template3: TButton;
    BTN_waves_clear: TButton;
    BTN_signal_xy_clear: TButton;
    BTN_signal_xy_template1: TButton;
    BTN_signal_xy_template2: TButton;
    BTN_spectrum_syntesis: TButton;
    BTN_waves_template1: TButton;
    BTN_spectrum_analisys: TButton;
    BTN_waves_N: TButton;
    Btn_reset_t: TButton;
    BTN_waves_rnd: TButton;
    BTN_syntes_img_waves: TButton;
    BTN_signal_Nx_Ny: TButton;
    BTN_waves_template2: TButton;
    CB_timer: TCheckBox;
    CB_waves_legend: TCheckBox;
    CB_z_level: TCheckBox;
    CB_ab_phi_model: TCheckBox;
    CB_z_waves: TCheckBox;
    Edit_waves_width: TEdit;
    Edit_waves_sx: TEdit;
    Edit_waves_height: TEdit;
    Edit_waves_sy: TEdit;
    Edit_w1: TEdit;
    Edit_t: TEdit;
    Edit_dt: TEdit;
    Edit_Waves_N: TEdit;
    Edit_k_dist: TEdit;
    Edit_signal_Nx: TEdit;
    Label1: TLabel;
    Label10: TLabel;
    LBL_img_waves_x: TLabel;
    Label11: TLabel;
    LBL_img_waves_y: TLabel;
    LBL_img_waves_XY_val: TLabel;
    Label2: TLabel;
    Label3: TLabel;
    Label4: TLabel;
    Label5: TLabel;
    Label6: TLabel;
    Label7: TLabel;
    Label8: TLabel;
    Label9: TLabel;
    PBox: TPaintBox;
    SG_waves: TStringGrid;
    SG_signal_xy: TStringGrid;
    Timer1: TTimer;
    UpDown_sy: TUpDown;
    UpDown_sx: TUpDown;
    procedure BTN_signal_xy_randomClick(Sender: TObject);
    procedure BTN_signal_xy_template3Click(Sender: TObject);
    procedure BTN_waves_clearClick(Sender: TObject);
    procedure Btn_reset_tClick(Sender: TObject);
    procedure BTN_syntes_img_wavesClick(Sender: TObject);
    procedure BTN_waves_rndClick(Sender: TObject);
    procedure BTN_signal_Nx_NyClick(Sender: TObject);
    procedure BTN_signal_xy_template1Click(Sender: TObject);
    procedure BTN_signal_xy_template2Click(Sender: TObject);
    procedure BTN_spectrum_analisysClick(Sender: TObject);
    procedure BTN_signal_xy_clearClick(Sender: TObject);
    procedure BTN_spectrum_syntesisClick(Sender: TObject);
    procedure BTN_waves_NClick(Sender: TObject);
    procedure BTN_waves_template1Click(Sender: TObject);
    procedure BTN_waves_template2Click(Sender: TObject);
    procedure CB_ab_phi_modelChange(Sender: TObject);
    procedure CB_timerChange(Sender: TObject);
    procedure CB_waves_legendChange(Sender: TObject);
    procedure CB_z_levelChange(Sender: TObject);
    procedure CB_z_wavesChange(Sender: TObject);
    procedure FormCreate(Sender: TObject);
    procedure PBoxMouseMove(Sender: TObject; Shift: TShiftState; X, Y: Integer);
    procedure PBoxPaint(Sender: TObject);
    procedure Timer1Timer(Sender: TObject);
    procedure UpDown_sxClick(Sender: TObject; Button: TUDBtnType);
    procedure UpDown_syClick(Sender: TObject; Button: TUDBtnType);
  private
    procedure Draw_img_waves;
    procedure print_params;
    procedure get_params;
  public

  end;

type
TComplex=record
   re,im:real;
end;
type TComplexVector=array of TComplex;

const MAX_WAVES=1024;
const MAX_SIGNALS=1024;

type
  t_wave=record
    xb,yb:real;
    f:real;
    amp:real;
    phi:real;
    a,b:real;
  end;

var
  Form1: TForm1;
  init_flag:boolean;
  legend_flag, Z_level_flag, Z_waves_flag, ab_flag:boolean;
  MouseX, MouseY: integer; MouseShift:TShiftState;
  SummaryBitmap:TBitmap;
  img_width,img_height:integer;

  t,dt:real;
  waves_sx,waves_sy:real;
  waves_width,waves_height:integer;
  k_dist,dx,dy:real;
  N_waves: integer;
  waves: array[0..MAX_WAVES] of t_wave;
  IMG_waves: array[0..MAX_WAVES,0..MAX_WAVES]of real;

  signal_nx: integer;
  signal_xy:array[0..MAX_SIGNALS] of TComplex;
  fourie_w1:real;

implementation

{$R *.lfm}

function c_add(a,b:TComplex):TComplex;
begin c_add.re:=a.re+b.re; c_add.im:=a.im+b.im; end;

function c_mul(a,b:TComplex):TComplex;
begin c_mul.re:=a.re*b.re-a.im*b.im; c_mul.im:=a.re*b.im+a.im*b.re; end;

function c_root_of_one_CW(k,n:integer):TComplex;
var phi:real;
begin
     phi:=-2*PI*k/n;
     c_root_of_one_CW.re:=cos(phi);
     c_root_of_one_CW.im:=sin(phi);
end;

function c_root_of_one_CCW(k,n:integer):TComplex;
var phi:real;
begin
     phi:=2*PI*k/n;
     c_root_of_one_CCW.re:=cos(phi);
     c_root_of_one_CCW.im:=sin(phi);
end;

//преобразование Фурье (спектральный анализ)
//медленный алгоритм со степенью сложности O(N*N)
//память для DFT_t и DFT_f должна быть выделена до вызова подпрограммы
procedure DFT_analysis_slow(var DFT_t,DFT_f:TComplexVector);
var k,j,N,M:integer;
begin
  N:=length(DFT_t);
  M:=length(DFT_f);
  for k:=0 to M-1 do
  begin
     DFT_f[k].re:=0; DFT_f[k].im:=0;
     for j:=0 to N-1 do
        DFT_f[k]:=c_add(DFT_f[k],c_mul(DFT_t[j],c_root_of_one_CW(k*j,N)));
     DFT_f[k].re:=DFT_f[k].re/M;
     DFT_f[k].im:=DFT_f[k].im/M;
  end;
end;

//преобразование Фурье (спектральный синтез)
//медленный алгоритм со степенью сложности O(N*N)
//память для DFT_t и DFT_f должна быть выделена до вызова подпрограммы
procedure DFT_syntesis_slow(var DFT_f,DFT_t:TComplexVector);
var k,j,N,M:integer;
begin
  N:=length(DFT_t);
  M:=length(DFT_f);
  for j:=0 to N-1 do
  begin
    DFT_t[j].re:=0; DFT_t[j].im:=0;
    for k:=0 to M-1 do
      DFT_t[j]:=c_add(DFT_t[j],c_mul(DFT_f[k],c_root_of_one_CCW(k*j,N)));
  end;
end;
//========================================================================

procedure calc_ab_from_phiamp(var w:t_wave);
begin
    w.a:=w.amp*cos(w.phi);
    w.b:=-w.amp*sin(w.phi);
end;

procedure calc_phiamp_from_ab(var w:t_wave);
begin
    w.amp:=sqrt(sqr(w.a)+sqr(w.b));
    if w.a<>0
    then
      begin
        w.phi:=abs(arctan(w.b/w.a));
        if (w.a<0)and(w.b<0) then w.phi:=pi-w.phi;
        if (w.a>0)and(w.b>0) then w.phi:=-w.phi;
        if (w.a<0)and(w.b>0) then w.phi:=-pi+w.phi;
      end
    else
      begin
        if w.b>0 then w.phi:=pi/2;
        if w.b<0 then w.phi:=-pi/2;
        if w.b=0 then w.phi:=0;
      end;
end;

procedure correction_ab_phi;
var k:integer;
begin
  if ab_flag then for k:=0 to N_waves-1 do calc_phiamp_from_ab(waves[k])
             else for k:=0 to N_waves-1 do calc_ab_from_phiamp(waves[k]);
end;

procedure clr_waves;
var k:integer;
begin
  for k:=0 to N_waves-1 do
  begin
    waves[k].xb:=0;
    waves[k].yb:=0;
    waves[k].amp:=0;
    waves[k].f:=0;
    waves[k].phi:=0;
    waves[k].a:=0;
    waves[k].b:=0;
  end;
end;

procedure clr_signal;
var i:integer;
begin
  for i:=0 to signal_nx-1 do
  begin
    signal_xy[i].re:=0;
    signal_xy[i].im:=0;
  end;
end;

procedure spectrum_analisys;
var i,k:integer; DFT_f,DFT_t:TComplexVector;
begin
  setlength(DFT_f,N_waves);
  setlength(DFT_t,signal_nx);

  for i:=0 to signal_nx-1 do DFT_t[i]:=signal_xy[i];

  DFT_analysis_slow(DFT_t,DFT_f);

  for k:=0 to N_waves-1 do
  begin
    waves[k].f:=fourie_w1*k;
    waves[k].a:=DFT_f[k].re;
    waves[k].b:=DFT_f[k].im;
    calc_phiamp_from_ab(waves[k]);
  end;

  setlength(DFT_f,0);
  setlength(DFT_t,0);
end;

procedure spectrum_syntesis;
var i,k:integer; DFT_f,DFT_t:TComplexVector; w:t_wave;
begin
  setlength(DFT_f,N_waves);
  setlength(DFT_t,signal_nx);

  for k:=0 to N_waves-1 do
  begin
    w:=waves[k];
    if not(ab_flag) then calc_ab_from_phiamp(w);
    DFT_f[k].re:=w.a;
    DFT_f[k].im:=w.b;
  end;

  DFT_syntesis_slow(DFT_f,DFT_t);

  for i:=0 to signal_nx-1 do signal_xy[i]:=DFT_t[i];

  setlength(DFT_f,0);
  setlength(DFT_t,0);
end;

function wave_sin(w:t_wave; t:real):real;
begin wave_sin:=w.amp*sin(w.f*t+w.phi); end;

function wave_sin0(w:t_wave; t:real):real;
begin wave_sin0:=w.amp*sin(w.f*t); end;

function wave_cos(w:t_wave; t:real):real;
begin wave_cos:=w.amp*cos(w.f*t+w.phi); end;

function wave_cos0(w:t_wave; t:real):real;
begin wave_cos0:=w.amp*cos(w.f*t); end;

procedure gen_img_waves;
var k,x,y:integer; w:t_wave; dist_t,tmp_amp,xr,yr:real;
begin
  for x:=0 to waves_width-1 do
  for y:=0 to waves_height-1 do
  begin
    IMG_waves[x,y]:=0;
    xr:=x/k_dist+waves_sx;
    yr:=y/k_dist+waves_sy;
    for k:=0 to N_waves-1 do
    begin
      dist_t:=sqrt(sqr(xr-waves[k].xb)+sqr(yr-waves[k].yb));
      tmp_amp:=wave_cos(waves[k],t+dist_t);
      IMG_waves[x,y]:=IMG_waves[x,y]+tmp_amp;
    end;
  end;
end;

{ TForm1 }
procedure TForm1.get_params;
var i,j,k:integer;
begin
  legend_flag:=CB_waves_legend.Checked;
  z_level_flag:=CB_z_level.Checked;
  ab_flag:=CB_ab_phi_model.Checked;
  z_waves_flag:=CB_z_waves.Checked;

  N_waves:=StrToInt(Edit_Waves_N.text);
  if N_waves<1 then N_waves:=1;
  if N_waves>MAX_WAVES then N_waves:=MAX_WAVES;

  fourie_w1:=StrToFloat(Edit_w1.text);

  waves_sx:=StrToFloat(Edit_waves_sx.text);
  waves_sy:=StrToFloat(Edit_waves_sy.text);

  waves_width:=StrToInt(Edit_waves_width.text);
  if waves_width<1 then waves_width:=1;
  if waves_width>MAX_WAVES then waves_width:=MAX_WAVES;
  waves_height:=StrToInt(Edit_waves_height.text);
  if waves_height<1 then waves_height:=1;
  if waves_height>MAX_WAVES then waves_height:=MAX_WAVES;

  dx:=img_width div waves_width;
  dy:=img_height div waves_height;

  t:=StrToFloat(Edit_t.text);
  dt:=StrToFloat(Edit_dt.text);

  k_dist:=StrToFloat(Edit_k_dist.text);
  if k_dist<0 then k_dist:=1;

  for k:=0 to N_waves-1 do
  begin
    waves[k].xb:=StrToFloat(SG_waves.Cells[1,k+1]);
    waves[k].yb:=StrToFloat(SG_waves.Cells[2,k+1]);
    waves[k].f:=StrToFloat(SG_waves.Cells[3,k+1]);
    waves[k].amp:=StrToFloat(SG_waves.Cells[4,k+1]);
    waves[k].phi:=StrToFloat(SG_waves.Cells[5,k+1]);
    waves[k].a:=StrToFloat(SG_waves.Cells[6,k+1]);
    waves[k].b:=StrToFloat(SG_waves.Cells[7,k+1]);
  end;
  correction_ab_phi;

  signal_nx:=StrToInt(Edit_signal_Nx.text);
  if signal_nx<1 then signal_nx:=1;
  if signal_nx>MAX_SIGNALS then signal_nx:=MAX_SIGNALS;

  for i:=0 to signal_nx-1 do
  begin
    signal_xy[i].re:=StrToFloat(SG_signal_xy.Cells[i+1,1]);
    signal_xy[i].im:=StrToFloat(SG_signal_xy.Cells[i+1,2]);
  end;
end;

procedure TForm1.print_params;
var i,j,k:integer;
begin
  CB_waves_legend.Checked:=legend_flag;
  CB_z_level.Checked:=z_level_flag;
  CB_ab_phi_model.Checked:=ab_flag;
  CB_z_waves.Checked:=z_waves_flag;

  Edit_Waves_N.text:=IntToStr(N_waves);

  Edit_waves_sx.text:=FloatToStr(waves_sx);
  Edit_waves_sy.text:=FloatToStr(waves_sy);

  UpDown_sx.Position:=trunc(waves_sx);
  UpDown_sy.Position:=trunc(waves_sy);

  Edit_waves_width.text:=IntToStr(waves_width);
  Edit_waves_height.text:=IntToStr(waves_height);

  Edit_t.text:=FloatToStrF(t,ffFixed,1,5);
  Edit_dt.text:=FloatToStr(dt);
  Edit_k_dist.text:=FloatToStrF(k_dist,ffFixed,1,3);
  Edit_w1.text:=FloatToStrF(fourie_w1,ffFixed,1,3);

  for k:=0 to N_waves-1 do
  begin
    SG_waves.Cells[0,k+1]:=IntToStr(k);
    SG_waves.Cells[1,k+1]:=FloatToStrF(waves[k].xb,ffFixed,1,5);
    SG_waves.Cells[2,k+1]:=FloatToStrF(waves[k].yb,ffFixed,1,5);
    SG_waves.Cells[3,k+1]:=FloatToStrF(waves[k].f,ffFixed,1,5);
    SG_waves.Cells[4,k+1]:=FloatToStrF(waves[k].amp,ffFixed,1,5);
    SG_waves.Cells[5,k+1]:=FloatToStrF(waves[k].phi,ffFixed,1,5);
    SG_waves.Cells[6,k+1]:=FloatToStrF(waves[k].a,ffFixed,1,5);
    SG_waves.Cells[7,k+1]:=FloatToStrF(waves[k].b,ffFixed,1,5);
  end;

  Edit_signal_Nx.text:=IntToStr(signal_nx);

  for i:=0 to signal_nx-1 do SG_signal_xy.Cells[i+1,0]:=IntToStr(i);

  for i:=0 to signal_nx-1 do
  begin
    SG_signal_xy.Cells[i+1,1]:=FloatToStrF(signal_xy[i].re,ffFixed,1,3);
    SG_signal_xy.Cells[i+1,2]:=FloatToStrF(signal_xy[i].im,ffFixed,1,3);
  end;
end;

procedure TForm1.Draw_img_waves;
var k,x,y:integer; c:byte; tmp:LongInt; dst_ptr:PByte; dst_bpp:integer;
  amp,dist_t,xr,yr:real;
begin
  SummaryBitmap.BeginUpdate(false);
  dst_bpp:=SummaryBitmap.RawImage.Description.BitsPerPixel div 8;
  dst_ptr:=SummaryBitmap.RawImage.Data;
  for y:=img_height-1 downto 0 do
  for x:=0 to img_width-1 do
  begin
    C:=0; tmp:=trunc(IMG_waves[trunc(x/dx),trunc(y/dy)])+128;
    if (tmp>=0)and(tmp<=255) then C:=tmp;
    if tmp<0 then C:=0;
    if tmp>255 then C:=255;
    dst_ptr^:=C; (dst_ptr+1)^:=C; (dst_ptr+2)^:=C;
    inc(dst_ptr,dst_bpp);
  end;
  SummaryBitmap.EndUpdate(false);
  PBox.Canvas.Draw(0,0,SummaryBitmap);

  if legend_flag then
  begin
    PBox.Canvas.Pen.Color:=clRed;
    PBox.Canvas.Brush.Style:=bsClear;
    PBox.Canvas.Font.Color:=clRed;
    for k:=0 to N_waves-1 do
    begin
      x:=trunc(dx*k_dist*(waves[k].xb-waves_sx));
      y:=trunc(dy*k_dist*(waves[k].yb-waves_sy));
      PBox.Canvas.EllipseC(x,PBox.Height-y,trunc(waves[k].amp),trunc(waves[k].amp));
      PBox.Canvas.TextOut(x,PBox.Height-y,IntToStr(k));
    end;
  end;

  if z_level_flag or z_waves_flag then
  begin
    PBox.Canvas.Pen.Color:=clYellow;
    for k:=-10 to 10 do
    begin
      PBox.Canvas.TextOut(0,PBox.Height div 2 - k*25,IntToStr(k*25));
      PBox.Canvas.Line(0,PBox.Height div 2 - k*25,PBox.Width-1,PBox.Height div 2 - k*25);
    end;
    PBox.Canvas.Pen.Color:=clRed;
    PBox.Canvas.Line(0,MouseY,PBox.Width-1,MouseY);
  end;

  if z_level_flag then
  begin
    PBox.Canvas.Pen.Color:=clBlue;
    PBox.Canvas.MoveTo(0,PBox.Height div 2);
    for x:=0 to waves_width-1 do
    begin
      amp:=IMG_waves[x,trunc((PBox.Height-MouseY)/dy)];
      PBox.Canvas.LineTo(trunc(dx*x),PBox.Height div 2 - trunc(amp));
    end;
  end;

  if z_waves_flag then
  begin
    yr:=(PBox.height-MouseY)/(dy*k_dist)+waves_sy;
    for k:=0 to N_waves-1 do
    begin
      PBox.Canvas.Pen.Color:=clGreen;
      PBox.Canvas.MoveTo(0,PBox.Height div 2);
      for x:=0 to waves_width-1 do
      begin
        xr:=x/k_dist+waves_sx;
        dist_t:=sqrt(sqr(xr-waves[k].xb)+sqr(yr-waves[k].yb));
        amp:=wave_cos(waves[k],t+dist_t);
        PBox.Canvas.LineTo(trunc(x*dx),PBox.Height div 2 - trunc(amp));
      end;
    end;
  end;
end;

procedure TForm1.BTN_spectrum_analisysClick(Sender: TObject);
begin
  get_params;
  spectrum_analisys;
  print_params;
  get_params;
  print_params;
  gen_img_waves;
  Draw_img_waves;
end;

procedure TForm1.BTN_spectrum_syntesisClick(Sender: TObject);
begin
  get_params;
  spectrum_syntesis;
  print_params;
  get_params;
  print_params;
end;

procedure TForm1.BTN_syntes_img_wavesClick(Sender: TObject);
begin
  get_params;
  gen_img_waves;
  Draw_img_waves;
  print_params;
end;

procedure TForm1.Btn_reset_tClick(Sender: TObject);
begin
  t:=0; Edit_t.text:=FloatToStr(t);
  get_params;
  print_params;
  gen_img_waves;
  Draw_img_waves;
end;

procedure TForm1.BTN_waves_NClick(Sender: TObject);
begin
  N_waves:=StrToInt(Edit_Waves_N.text);
  SG_waves.RowCount:=N_waves+1;
  print_params;
  get_params;
  print_params;
  gen_img_waves;
  Draw_img_waves;
end;

procedure TForm1.BTN_waves_template1Click(Sender: TObject);
var k:integer;
begin
  clr_waves;
  for k:=0 to 0 do
  begin
    waves[k].xb:=0;
    waves[k].yb:=0;
    waves[k].f:=1;
    waves[k].amp:=100;
    waves[k].phi:=0;
    calc_ab_from_phiamp(waves[k]);
  end;
  print_params;
  get_params;
  print_params;
  gen_img_waves;
  Draw_img_waves;
end;

procedure TForm1.BTN_waves_template2Click(Sender: TObject);
var k:integer;
begin
  clr_waves;
  for k:=0 to N_waves-1 do
  begin
    waves[k].xb:=(random(waves_width)-(waves_width div 2))/k_dist;
    waves[k].yb:=0;
    waves[k].f:=random(5)+1;
    waves[k].amp:=random(20)+20;
    waves[k].phi:=random()*2*pi-pi;
    calc_ab_from_phiamp(waves[k]);
  end;
  print_params;
  get_params;
  print_params;
  gen_img_waves;
  Draw_img_waves;
end;

procedure TForm1.BTN_waves_clearClick(Sender: TObject);
begin
  clr_waves;
  print_params;
  get_params;
  print_params;
  gen_img_waves;
  Draw_img_waves;
end;

procedure TForm1.BTN_waves_rndClick(Sender: TObject);
var k:integer;
begin
  for k:=0 to N_waves-1 do
  begin
    waves[k].xb:=(random()*waves_width-waves_width/2)/k_dist;
    waves[k].yb:=(random()*waves_height-waves_height/2)/k_dist;
    waves[k].f:=random(5)+1;
    waves[k].amp:=50*random();
    waves[k].phi:=2*pi*random()-pi;
    calc_ab_from_phiamp(waves[k]);
  end;
  print_params;
  get_params;
  print_params;
  gen_img_waves;
  Draw_img_waves;
end;

procedure TForm1.BTN_signal_Nx_NyClick(Sender: TObject);
begin
  signal_nx:=StrToInt(Edit_signal_Nx.text);
  SG_signal_xy.ColCount:=signal_nx+1;
  print_params;
end;

procedure TForm1.BTN_signal_xy_clearClick(Sender: TObject);
begin
  clr_signal;
  print_params;
end;

procedure TForm1.BTN_signal_xy_randomClick(Sender: TObject);
var i:integer;
begin
  clr_signal;
  for i:=0 to signal_nx-1 do
  begin
    signal_xy[i].re:=random(50)+50;
    signal_xy[i].im:=0;
  end;
  print_params;
end;

procedure TForm1.BTN_signal_xy_template1Click(Sender: TObject);
var i:integer;
begin
  clr_signal;
  for i:=0 to signal_nx-1 do
  begin
    signal_xy[i].re:=50;
    signal_xy[i].im:=0;
  end;
  print_params;
end;

procedure TForm1.BTN_signal_xy_template2Click(Sender: TObject);
begin
  clr_signal;
  signal_xy[1].re:=100;
  signal_xy[1].im:=0;
  print_params;
end;

procedure TForm1.BTN_signal_xy_template3Click(Sender: TObject);
var i:integer;
begin
  clr_signal;
  for i:=0 to signal_nx-1 do
  begin
    signal_xy[i].re:=0;
    signal_xy[i].im:=random(50)+50;
  end;
  print_params;
end;

procedure TForm1.CB_ab_phi_modelChange(Sender: TObject);
begin
  get_params;
  print_params;
  gen_img_waves;
  Draw_img_waves;
end;

procedure TForm1.CB_timerChange(Sender: TObject);
begin
  if CB_timer.Checked then Timer1.Enabled:=true else Timer1.Enabled:=false;
end;

procedure TForm1.CB_waves_legendChange(Sender: TObject);
begin
  get_params;
  gen_img_waves;
  Draw_img_waves;
end;

procedure TForm1.CB_z_levelChange(Sender: TObject);
begin
  MouseX:=255; MouseY:=255;
  get_params;
  gen_img_waves;
  Draw_img_waves;
end;

procedure TForm1.CB_z_wavesChange(Sender: TObject);
begin
  MouseX:=255; MouseY:=255;
  get_params;
  gen_img_waves;
  Draw_img_waves;
end;

procedure TForm1.FormCreate(Sender: TObject);
begin
  img_width:=PBox.width;
  img_height:=PBox.height;
  SummaryBitmap:=TBitmap.Create;
  SummaryBitmap.SetSize(img_width,img_height);

  timer1.Enabled:=false;
  N_waves:=16;
  signal_nx:=16;
  fourie_w1:=1;
  k_dist:=5;
  dt:=-0.1;

  waves_width:=64;
  waves_height:=64;

  waves_sx:=-waves_width/(k_dist*2);
  waves_sy:=-waves_height/(k_dist*2);

  dx:=img_width/waves_width;
  dy:=img_height/waves_height;

  SG_waves.RowCount:=N_waves+1;
  SG_waves.Cells[0,0]:='';
  SG_waves.Cells[1,0]:='Xb';
  SG_waves.Cells[2,0]:='Yb';
  SG_waves.Cells[3,0]:='f';
  SG_waves.Cells[4,0]:='amp';
  SG_waves.Cells[5,0]:='phi';
  SG_waves.Cells[6,0]:='a';
  SG_waves.Cells[7,0]:='b';
  clr_waves;

  SG_signal_xy.ColCount:=signal_nx+1;

  SG_signal_xy.Cells[0,0]:='';
  SG_signal_xy.Cells[0,1]:='Re';
  SG_signal_xy.Cells[0,2]:='Im';
  clr_signal;

  print_params;
  get_params;
  print_params;
  gen_img_waves;
  //Draw_img_waves;
  init_flag:=true;
end;

procedure TForm1.PBoxMouseMove(Sender: TObject; Shift: TShiftState; X,Y: Integer);
var xr,yr:real;
begin
  MouseX:=X; MouseY:=Y; MouseShift:=Shift;
  xr:=MouseX/(dx*k_dist)+waves_sx;
  yr:=(PBox.Height-MouseY)/(dy*k_dist)+waves_sy;
  LBL_img_waves_x.caption:='x='+FloatToStrF(xr,ffFixed,1,1);
  LBL_img_waves_y.caption:='y='+FloatToStrF(yr,ffFixed,1,1);
  LBL_img_waves_XY_val.caption:='amp='+
                FloatToStrF(IMG_waves[trunc(MouseX/dx),
                                      trunc((PBox.Height-MouseY)/dy)],
                            ffFixed,1,2);

  if Z_level_flag or Z_waves_flag then Draw_img_waves;
end;

procedure TForm1.PBoxPaint(Sender: TObject);
begin
  if init_flag then
  begin
    gen_img_waves;
    Draw_img_waves;
  end;
end;

procedure TForm1.Timer1Timer(Sender: TObject);
begin
  t:=t+dt; Edit_t.Text:=floatToStr(t);
  get_params;
  gen_img_waves;
  if not(CB_z_level.checked) then Draw_img_waves;
  PBoxMouseMove(self,MouseShift,MouseX,MouseY);
  print_params;
end;

procedure TForm1.UpDown_sxClick(Sender: TObject; Button: TUDBtnType);
begin
  Edit_waves_sx.Text:=IntToStr(UpDown_sx.Position);
  get_params;
  gen_img_waves;
  Draw_img_waves;
  print_params;
end;

procedure TForm1.UpDown_syClick(Sender: TObject; Button: TUDBtnType);
begin
  Edit_waves_sy.Text:=IntToStr(UpDown_sy.Position);
  get_params;
  gen_img_waves;
  Draw_img_waves;
  print_params;
end;

end.

