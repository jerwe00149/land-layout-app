import os
import json

import streamlit as st

# 資料持久化
DATA_FILE = '/tmp/land_data.json'

def load_saved_data():
    """載入保存的地號資料"""
    if os.path.exists(DATA_FILE):
        try:
            with open(DATA_FILE, 'r', encoding='utf-8') as f:
                return json.load(f)
        except:
            return {}
    return {}

def save_data(data):
    """保存地號資料"""
    try:
        with open(DATA_FILE, 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except Exception as e:
        st.error(f"保存失敗: {e}")

# 程式啟動時載入資料
if 'lots_data' not in st.session_state:
    saved = load_saved_data()
    if saved:
        st.session_state.update(saved)
        st.sidebar.success("✅ 已載入上次的地號資料")

def block_id_to_letter(block_id):
    """将数字区块ID转换为字母（1->A, 2->B, ...）"""
    return chr(64 + block_id)  # 65 is 'A'


def merge_small_lots_into_neighbors(lots, min_ping):
    """把小於最小坪數的灰色畸零地，僅在「相鄰接觸」時併入同街廓地塊。"""
    if not lots:
        return lots

    def unpack(lot_tuple):
        if len(lot_tuple) == 4:
            return lot_tuple[0], lot_tuple[1], lot_tuple[2], lot_tuple[3]
        return lot_tuple[0], lot_tuple[1], lot_tuple[2], 1

    parsed = [list(unpack(t)) for t in lots]  # [poly, dx, dy, bid]

    valid_idx, small_idx = [], []
    for i, (poly, dx, dy, bid) in enumerate(parsed):
        area_ping = poly.area * 0.3025
        if area_ping >= min_ping:
            valid_idx.append(i)
        else:
            small_idx.append(i)

    if not small_idx or not valid_idx:
        return lots

    removed = set()
    eps = 1e-6

    for si in small_idx:
        if si in removed:
            continue
        spoly, sdx, sdy, sbid = parsed[si]

        # 只找同街廓且「接觸」的候選，避免跨塊吃到上方地塊
        candidates = []
        for vi in valid_idx:
            if vi in removed:
                continue
            vpoly, vdx, vdy, vbid = parsed[vi]
            if vbid != sbid:
                continue
            if spoly.distance(vpoly) > eps:
                continue

            inter = spoly.boundary.intersection(vpoly.boundary)
            shared_len = inter.length if not inter.is_empty else 0.0
            candidates.append((shared_len, vi))

        if not candidates:
            # 沒有可安全合併的相鄰地塊，就保留灰地，不強行併
            continue

        # 優先併入共邊最長的地塊（通常就是正確鄰地，例如 D-6）
        candidates.sort(key=lambda x: x[0], reverse=True)
        target_i = candidates[0][1]
        tpoly, tdx, tdy, tbid = parsed[target_i]

        merged = tpoly.union(spoly)
        if merged.geom_type == 'MultiPolygon':
            # 只在連通時才應發生；保守取最大塊避免異常
            merged = max(list(merged.geoms), key=lambda g: g.area)

        parsed[target_i][0] = merged
        removed.add(si)

    out = []
    for i, (poly, dx, dy, bid) in enumerate(parsed):
        if i in removed:
            continue
        out.append((poly, dx, dy, bid))

    return out


import math
import matplotlib.pyplot as plt
from shapely.geometry import Polygon, box
import shapely.ops
import shapely.affinity


def configured_road_width_for_polygon(r, roads_info):
    """依道路方向/位置，從左側設定 roads_info 取對應路寬。"""
    if not roads_info:
        return None
    r_minx, r_miny, r_maxx, r_maxy = r.bounds
    rc = r.centroid
    # 道路長向判斷：高>寬 視為直向(V)，反之橫向(H)
    is_vertical = (r_maxy - r_miny) > (r_maxx - r_minx)

    candidates = []
    for info in roads_info:
        if len(info) < 3:
            continue
        typ, pos, w = info[0], float(info[1]), float(info[2])
        if is_vertical and typ == 'V':
            candidates.append((abs(rc.x - pos), w))
        if (not is_vertical) and typ == 'H':
            candidates.append((abs(rc.y - pos), w))

    if not candidates:
        return None
    candidates.sort(key=lambda x: x[0])
    return candidates[0][1]


def road_width_from_polygon(poly):
    """估算道路寬度：取最小外接旋轉矩形的短邊。"""
    try:
        mrr = poly.minimum_rotated_rectangle
        coords = list(mrr.exterior.coords)
        if len(coords) < 5:
            return 0.0
        import math
        lens = []
        for i in range(4):
            x1, y1 = coords[i]
            x2, y2 = coords[i+1]
            lens.append(math.hypot(x2-x1, y2-y1))
        return float(min(lens))
    except Exception:
        return 0.0

def get_polygon_coords(poly):
    if poly.geom_type == 'MultiPolygon':
        x, y = [], []
        for p in poly.geoms:
            px, py = p.exterior.xy
            x.extend(px)
            x.append(None)
            y.extend(py)
            y.append(None)
        return x, y
    elif poly.geom_type == 'Polygon':
        return poly.exterior.xy
    return [], []

import numpy as np
import pandas as pd
import json
import ezdxf
import tempfile
import zipfile
import os

def read_plines(doc):
    layers = {}
    for e in doc.modelspace():
        try:
            t = e.dxftype()
            if t == 'LWPOLYLINE':
                pts = [(p[0],p[1]) for p in e.get_points(format='xy')]
            elif t == 'POLYLINE':
                pts = [(float(v.dxf.location.x),float(v.dxf.location.y)) for v in e.vertices]
            else: continue
            if len(pts)>=3:
                layers.setdefault(e.dxf.layer,[]).append(pts)
        except: pass
    return layers

def hull(points):
    pts = sorted(set(points))
    if len(pts)<=2: return pts
    def cr(o,a,b): return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])
    lo,up=[],[]
    for p in pts:
        while len(lo)>=2 and cr(lo[-2],lo[-1],p)<=0: lo.pop()
        lo.append(p)
    for p in reversed(pts):
        while len(up)>=2 and cr(up[-2],up[-1],p)<=0: up.pop()
        up.append(p)
    return lo[:-1]+up[:-1]


import io

plt.rcParams['font.sans-serif'] = ['Arial Unicode MS', 'Heiti TC', 'PingFang HK', 'DejaVu Sans']
plt.rcParams['axes.unicode_minus'] = False

st.set_page_config(page_title="自動割豆腐排平圖系統", layout="wide")

st.markdown("""
<style>
    [data-testid="stSidebar"] { width: 340px !important; }
    /* 只縮小側邊欄的字體，避免主標題被切割 */
    [data-testid="stSidebar"] h1, [data-testid="stSidebar"] h2, [data-testid="stSidebar"] h3 { font-size: 15px !important; }
    .block-container { 
        padding-top: 2rem !important; 
        padding-bottom: 1rem !important; 
        padding-left: 2rem !important; 
        padding-right: 2rem !important; 
        max-width: 1200px !important; 
        margin: 0 auto;
    }
</style>
""", unsafe_allow_html=True)


def generate_dxf(base_poly, lots, roads_poly_list, coverage_ratio, min_ping):
    doc = ezdxf.new('R2013')
    dxf_block_counts = {}
    
    # 建立圖層與顏色 (1:紅, 2:黃, 3:綠, 4:青, 5:藍, 6:洋紅, 7:白, 8:灰)
    doc.layers.add('SITE_BOUNDARY', color=1)
    doc.layers.add('LOTS', color=3)
    doc.layers.add('BUILDING', color=5)
    doc.layers.add('ROAD', color=8)
    doc.layers.add('DIMENSION', color=1)
    doc.layers.add('TEXT', color=7)
    
    msp = doc.modelspace()
    
    # 畫基地外框
    if base_poly.geom_type == 'Polygon':
        pts = list(base_poly.exterior.coords)
        msp.add_lwpolyline([(p[0]*100, p[1]*100) for p in pts], close=True, dxfattribs={'layer': 'SITE_BOUNDARY'})
        
    # 畫道路
    for r in roads_poly_list:
        if r.geom_type == 'Polygon':
            pts = list(r.exterior.coords)
            msp.add_lwpolyline([(p[0]*100, p[1]*100) for p in pts], close=True, dxfattribs={'layer': 'ROAD'})
            
    # 畫土地與建築物
    for lot_tuple in lots:
        if len(lot_tuple) == 4:
            lot, arrow_dx, arrow_dy, block_id = lot_tuple
        else:
            lot, arrow_dx, arrow_dy = lot_tuple
            block_id = 1
        area_ping = lot.area * 0.3025
        if area_ping < min_ping: continue
        
        # 土地
        if lot.geom_type == 'Polygon':
            pts = list(lot.exterior.coords)
            msp.add_lwpolyline([(p[0]*100, p[1]*100) for p in pts], close=True, dxfattribs={'layer': 'LOTS'})
            
        lot_minx, lot_miny, lot_maxx, lot_maxy = lot.bounds
        if abs(arrow_dx) > abs(arrow_dy):
            xf = coverage_ratio
            yf = 1.0
        else:
            xf = 1.0
            yf = coverage_ratio
            
        build_poly = shapely.affinity.scale(lot, xfact=xf, yfact=yf, origin='centroid')
        build_poly = build_poly.intersection(lot)
        
        # 收集街廓面寬統計
        if block_id not in block_width_stats:
            block_width_stats[block_id] = []
        block_width_stats[block_id].append(round(lot_width, 1))
        
        # 建築物
        if build_poly.geom_type == 'Polygon':
            pts = list(build_poly.exterior.coords)
            msp.add_lwpolyline([(p[0]*100, p[1]*100) for p in pts], close=True, dxfattribs={'layer': 'BUILDING'})
            
        # 文字標籤（多行分開顯示避免重疊）
        centroid = lot.centroid
        build_ping = build_poly.area * 0.3025
        
        # 使用block_counts統計區內編號
        if 'dxf_block_counts' not in locals():
            dxf_block_counts = {}
        dxf_block_counts[block_id] = dxf_block_counts.get(block_id, 0) + 1
        
        # 分三行顯示：編號、土地面積、建築面積
        msp.add_text(f"{block_id_to_letter(block_id)}區-{dxf_block_counts[block_id]}", dxfattribs={'layer': 'TEXT', 'height': 60}).set_placement((centroid.x*100-150, centroid.y*100+100))
        msp.add_text(f"土地:{area_ping:.1f}p", dxfattribs={'layer': 'TEXT', 'height': 50}).set_placement((centroid.x*100-150, centroid.y*100))
        msp.add_text(f"建築:{build_ping:.1f}p", dxfattribs={'layer': 'TEXT', 'height': 50}).set_placement((centroid.x*100-150, centroid.y*100-100))
        
        # 面寬標線
        b_minx, b_miny, b_maxx, b_maxy = build_poly.bounds
        if abs(arrow_dx) > abs(arrow_dy):
            dim_x = b_minx if arrow_dx < 0 else b_maxx
            b_width = b_maxy - b_miny
            msp.add_line((dim_x*100, b_miny*100), (dim_x*100, b_maxy*100), dxfattribs={'layer': 'DIMENSION'})
            msp.add_text(f"{b_width:.1f}m", dxfattribs={'layer': 'TEXT', 'height': 40}).set_placement((dim_x*100+10, centroid.y*100))
        else:
            dim_y = b_miny if arrow_dy < 0 else b_maxy
            b_width = b_maxx - b_minx
            msp.add_line((b_minx*100, dim_y*100), (b_maxx*100, dim_y*100), dxfattribs={'layer': 'DIMENSION'})
            msp.add_text(f"{b_width:.1f}m", dxfattribs={'layer': 'TEXT', 'height': 40}).set_placement((centroid.x*100, dim_y*100+10))
            
    with tempfile.NamedTemporaryFile(delete=False, suffix='.dxf') as tmp:
        doc.saveas(tmp.name)
        return tmp.name

def generate_layout(poly, w, d, roads_info, min_area, auto_orient, auto_merge, block_params=None, custom_widths=None):
    bounds = poly.bounds
    if not bounds: return [], []
    minx, miny, maxx, maxy = bounds
    
    roads = []
    for r in roads_info:
        r_type, r_pos, r_width = r
        if r_type == 'V':
            r_box = box(r_pos, miny-50, r_pos + r_width, maxy+50)
        else:
            r_box = box(minx-50, r_pos, maxx+50, r_pos + r_width)
            
        road_poly = poly.intersection(r_box)
        if not road_poly.is_empty:
            if road_poly.geom_type == 'Polygon': roads.append(road_poly)
            else: roads.extend([geom for geom in road_poly.geoms if geom.area > 0.1])

    roads_poly = shapely.ops.unary_union(roads) if roads else Polygon()
    blocks_poly = poly.difference(roads_poly)
    
    lots = []
    block_id = 1
    if not blocks_poly.is_empty:
        # 對街廓幾何排序（左→右，下→上），確保 block_id 在 DXF 匯入前後保持一致
        if blocks_poly.geom_type == 'Polygon':
            block_geoms = [blocks_poly]
        else:
            block_geoms = sorted(
                list(blocks_poly.geoms),
                key=lambda g: (round(g.centroid.x, 1), round(g.centroid.y, 1))
            )
        
        for block in block_geoms:
            if block.area < 1.0:
                continue
                
            b_minx, b_miny, b_maxx, b_maxy = block.bounds
            bw = b_maxx - b_minx
            bh = b_maxy - b_miny
            
            # 使用街廓專屬參數（如果有設定的話）
            if block_params and block_id in block_params:
                block_w, block_d = block_params[block_id]
            else:
                block_w, block_d = w, d
            
            if auto_orient:
                if bw >= bh:
                    lot_w, lot_d = block_w, block_d
                    arrow_dx, arrow_dy = 0, -2
                else:
                    lot_w, lot_d = block_d, block_w
                    arrow_dx, arrow_dy = -2, 0
            else:
                lot_w, lot_d = block_w, block_d
                arrow_dx, arrow_dy = 0, -2

            curr_x = b_minx
            block_lots = []
            
            if bw >= bh:
                while curr_x < b_maxx:
                    nxt_x = curr_x + lot_w
                    if nxt_x >= b_maxx or (auto_merge and (b_maxx - nxt_x) * lot_d * 0.3025 < min_area):
                        nxt_x = b_maxx
                        
                    curr_y = b_miny
                    while curr_y < b_maxy:
                        nxt_y = curr_y + lot_d
                        if nxt_y >= b_maxy or (auto_merge and (b_maxy - nxt_y) * (nxt_x - curr_x) * 0.3025 < min_area):
                            nxt_y = b_maxy
                            
                        blade = box(curr_x, curr_y, nxt_x, nxt_y)
                        lot_raw = block.intersection(blade)
                        
                        if not roads_poly.is_empty:
                            lot = lot_raw.difference(roads_poly)
                        else:
                            lot = lot_raw
                            
                        if not lot.is_empty and lot.area > 0.1:
                            if lot.geom_type == 'Polygon': block_lots.append((lot, arrow_dx, arrow_dy))
                            else: block_lots.extend([(geom, arrow_dx, arrow_dy) for geom in lot.geoms if geom.area > 0.1])
                            
                        curr_y = nxt_y
                    curr_x = nxt_x
            else:
                curr_y = b_miny
                while curr_y < b_maxy:
                    nxt_y = curr_y + lot_d
                    if nxt_y >= b_maxy or (auto_merge and (b_maxy - nxt_y) * lot_w * 0.3025 < min_area):
                        nxt_y = b_maxy
                        
                    curr_x = b_minx
                    while curr_x < b_maxx:
                        nxt_x = curr_x + lot_w
                        if nxt_x >= b_maxx or (auto_merge and (b_maxx - nxt_x) * (nxt_y - curr_y) * 0.3025 < min_area):
                            nxt_x = b_maxx
                            
                        blade = box(curr_x, curr_y, nxt_x, nxt_y)
                        lot_raw = block.intersection(blade)
                        
                        if not roads_poly.is_empty:
                            lot = lot_raw.difference(roads_poly)
                        else:
                            lot = lot_raw
                            
                        if not lot.is_empty and lot.area > 0.1:
                            if lot.geom_type == 'Polygon': block_lots.append((lot, arrow_dx, arrow_dy))
                            else: block_lots.extend([(geom, arrow_dx, arrow_dy) for geom in lot.geoms if geom.area > 0.1])
                            
                        curr_x = nxt_x
                    curr_y = nxt_y


            # Merge leftovers to nearest valid lot
            valid_block_lots = []
            leftover_block_lots = []
            for lot, dx, dy in block_lots:
                if lot.area * 0.3025 >= min_area:
                    valid_block_lots.append((lot, dx, dy))
                else:
                    leftover_block_lots.append((lot, dx, dy))
                    
            if valid_block_lots:
                for leftover, _, _ in leftover_block_lots:
                    nearest_idx = min(range(len(valid_block_lots)), key=lambda i: valid_block_lots[i][0].distance(leftover))
                    v_lot, v_dx, v_dy = valid_block_lots[nearest_idx]
                    merged_lot = shapely.ops.unary_union([v_lot, leftover])
                    valid_block_lots[nearest_idx] = (merged_lot, v_dx, v_dy)
                for v_lot, v_dx, v_dy in valid_block_lots:
                    lots.append((v_lot, v_dx, v_dy, block_id))
            else:
                for leftover, dx, dy in leftover_block_lots:
                    lots.append((leftover, dx, dy, block_id))
            block_id += 1


    if roads:
        if roads_poly.geom_type == 'Polygon': roads = [roads_poly]
        elif roads_poly.geom_type == 'MultiPolygon': roads = list(roads_poly.geoms)

    return lots, roads

st.markdown("## 🏗️ 建築師排平圖系統 <span style='font-size: 14px; font-weight: normal; color: gray;'>（張哲維建築師事務所版權所有）</span>", unsafe_allow_html=True)

# DXF 匯入後清除舊 slider widget keys（必須在 widget 建立前執行）
if st.session_state.get('_dxf_clear_widget_keys', False):
    for k in list(st.session_state.keys()):
        if k.startswith(('vpos_', 'vw_', 'hpos_', 'hw_', 'bw_', 'bd_')):
            del st.session_state[k]
    st.session_state['_dxf_clear_widget_keys'] = False

with st.sidebar:
    st.markdown("### 1. 建築參數")
    width_req = st.number_input("基準面寬 (公尺)", min_value=3.0, max_value=20.0, value=st.session_state.get("width_req", 5.0), step=0.1)
    depth_req = st.number_input("基準深度 (公尺)", min_value=5.0, max_value=50.0, value=st.session_state.get("depth_req", 20.0), step=0.1)
    coverage_ratio = st.slider("建蔽率 (%)", min_value=0.0, max_value=100.0, value=float(st.session_state.get("coverage_ratio", 0.6) * 100), step=1.0) / 100
    min_ping = st.number_input("最小可建地坪", min_value=5.0, max_value=50.0, value=st.session_state.get("min_ping", 20.0), step=1.0)
    
    st.markdown("### 2. 土地檢討")
    auto_orient = st.checkbox("依街廓形狀自動轉向", value=st.session_state.get("auto_orient", True))
    auto_merge = st.checkbox("自動吸收邊角 (確保無剩餘碎地)", value=True)
    
    st.markdown("### 3. 手動配置多條道路")
    roads_info = st.session_state.get("roads_info", [])
    
    col_v, col_h = st.columns(2)
    with col_v:
        # 從 roads_info 推斷現有道路數量
        existing_v = sum(1 for r in roads_info if r[0] == "V") if roads_info else 0
        existing_h = sum(1 for r in roads_info if r[0] == "H") if roads_info else 0
        num_v_roads = st.number_input("直向道路數量", min_value=0, max_value=5, value=min(5, max(1, existing_v)), step=1)
    with col_h:
        num_h_roads = st.number_input("橫向道路數量", min_value=0, max_value=5, value=min(5, max(1, existing_h)), step=1)
        
    # 重新建立 roads_info
    new_roads_info = []
    
    if num_v_roads > 0:
        st.markdown("**直向道路設定 (垂直於X軸)**")
        # 取得現有的直向道路
        existing_v_roads = [r for r in roads_info if r[0] == 'V']
        for i in range(num_v_roads):
            # 如果有現有道路，使用其值；否則使用預設值
            default_pos = existing_v_roads[i][1] if i < len(existing_v_roads) else 30.0 + i*40.0
            default_w = existing_v_roads[i][2] if i < len(existing_v_roads) else 6.0
            
            v_pos = st.slider(f"直道 {i+1} 座標 (X)", 0.0, 150.0, default_pos, step=1.0, key=f"vpos_{i}")
            v_w = st.slider(f"直道 {i+1} 寬度", 1.5, 20.0, default_w, step=0.5, key=f"vw_{i}")
            new_roads_info.append(('V', v_pos, v_w))
            
    if num_h_roads > 0:
        st.markdown("**橫向道路設定 (垂直於Y軸)**")
        # 取得現有的橫向道路
        existing_h_roads = [r for r in roads_info if r[0] == 'H']
        for i in range(num_h_roads):
            # 如果有現有道路，使用其值；否則使用預設值
            default_pos = existing_h_roads[i][1] if i < len(existing_h_roads) else 45.0 + i*40.0
            default_w = existing_h_roads[i][2] if i < len(existing_h_roads) else 8.0
            
            h_pos = st.slider(f"橫道 {i+1} 座標 (Y)", 0.0, 150.0, default_pos, step=1.0, key=f"hpos_{i}")
            h_w = st.slider(f"橫道 {i+1} 寬度", 1.5, 20.0, default_w, step=0.5, key=f"hw_{i}")
            new_roads_info.append(('H', h_pos, h_w))
    
    # 更新 roads_info
    roads_info = new_roads_info

    st.markdown("### 上傳基地")
    uploaded_file = st.file_uploader("上傳基地檔案", type=['csv', 'json', 'dxf'], label_visibility="collapsed")

if 'base_coords' not in st.session_state:
    st.session_state.base_coords = [(0, 0), (120, 0), (130, 120), (20, 130), (0, 60)]

if uploaded_file is not None:
    # 使用文件ID或文件名+大小作为唯一标识
    file_id = getattr(uploaded_file, 'file_id', None) or f"{uploaded_file.name}_{uploaded_file.size}"
    
    # 只在文件真的改变时才重新处理
    if 'last_file_id' not in st.session_state or st.session_state.last_file_id != file_id:
        st.session_state.last_file_id = file_id
        
        try:
            if uploaded_file.name.endswith('.csv'):
                df = pd.read_csv(uploaded_file)
                st.session_state.base_coords = list(zip(df['X'], df['Y']))
            elif uploaded_file.name.endswith('.dxf'):
                with tempfile.NamedTemporaryFile(delete=False, suffix='.dxf') as tmp:
                    tmp.write(uploaded_file.getvalue())
                    tmp_path = tmp.name
                try:
                    doc = ezdxf.readfile(tmp_path)
                    layers = read_plines(doc)
                    land_key = None
                    for k in layers:
                        if 'U+5716' in k or '圖' in k: land_key=k; break
                    if not land_key and layers: land_key = max(layers, key=lambda k:len(layers[k]))
                    if land_key:
                        longest_pl = max(layers[land_key], key=len)
                        st.session_state.base_coords = [(p[0]/100.0, p[1]/100.0) for p in longest_pl]
                finally:
                    os.remove(tmp_path)
        except Exception as e:
            st.sidebar.warning(f"文件處理錯誤: {str(e)}")

base_coords = st.session_state.base_coords

base_polygon = Polygon(base_coords)

# 預先檢測街廓數量（DXF 模式用匯入資料，否則用參數預覽）
if st.session_state.get('loaded_from_dxf', False) and 'imported_lots' in st.session_state:
    lots_preview = st.session_state['imported_lots']
else:
    lots_preview, roads_preview = generate_layout(
        base_polygon, width_req, depth_req, 
        roads_info, min_ping, auto_orient, auto_merge
    )

# 統計街廓數量
block_ids = set()
for lot_tuple in lots_preview:
    if len(lot_tuple) == 4:
        _, _, _, bid = lot_tuple
        block_ids.add(bid)

num_blocks = len(block_ids)

# 為每個街廓提供獨立的面寬設定
if num_blocks > 1:
    with st.sidebar:
        st.markdown("---")
        st.markdown(f"### 4. 各街廓參數設定 ({num_blocks} 個街廓)")
        
        block_params = {}
        # 從 session_state 讀取已保存的街廓參數
        saved_block_params = st.session_state.get('block_params', {})
        
        for bid in sorted(block_ids):
            with st.expander(f"{block_id_to_letter(bid)}區 參數"):
                # 如果有保存的參數，使用之；否則使用預設值
                if str(bid) in saved_block_params:
                    default_w, default_d = saved_block_params[str(bid)]
                elif bid in saved_block_params:
                    default_w, default_d = saved_block_params[bid]
                else:
                    default_w, default_d = width_req, depth_req
                
                bw = st.number_input(f"{block_id_to_letter(bid)}區 面寬 (m)", min_value=3.0, max_value=20.0, value=float(default_w), step=0.1, key=f"bw_{bid}")
                bd = st.number_input(f"{block_id_to_letter(bid)}區 深度 (m)", min_value=5.0, max_value=50.0, value=float(default_d), step=0.1, key=f"bd_{bid}")
                block_params[bid] = (bw, bd)
else:
    block_params = None

# 檢查是否從 DXF 載入
if st.session_state.get('loaded_from_dxf', False):
    # DXF 模式：顯示精確幾何（與原圖一模一樣）
    lots = st.session_state.get('imported_lots', [])
    roads = st.session_state.get('imported_roads', [])
    st.info("📂 使用 DXF 匯入的幾何（原始佈局）")
    
    # 提供按鈕讓使用者切換到參數生成模式
    if st.button("🔄 使用左側參數重新生成佈局"):
        st.session_state['loaded_from_dxf'] = False
        st.rerun()
else:
    # 使用參數生成
    lots, roads = generate_layout(
        base_polygon, width_req, depth_req, 
        roads_info, min_ping, auto_orient, auto_merge, block_params
    , st.session_state.get("custom_lot_widths"))

# 將小塊灰地自動併入鄰近地塊
lots = merge_small_lots_into_neighbors(lots, min_ping)

# DEBUG: 顯示載入的地塊街廓分佈
_dbg_bids = {}
for _lt in lots:
    _bid = _lt[3] if len(_lt) == 4 else 0
    _dbg_bids[_bid] = _dbg_bids.get(_bid, 0) + 1
st.sidebar.info(f"🔍 渲染用街廓: {', '.join(f'{chr(64+k) if k>0 else "?"}'+'='+str(v) for k,v in sorted(_dbg_bids.items()))}")

# 顯示參考圖片（如果有）
if 'reference_image' in st.session_state:
    with st.expander("📷 參考圖片（匯入時的原始圖面）", expanded=False):
        st.image(st.session_state['reference_image'], caption="原始規劃圖面", width="stretch")
        st.caption("💡 可對照此圖微調參數")

fig, ax = plt.subplots(figsize=(10, 7))

# 1. 畫基地外框
x, y = get_polygon_coords(base_polygon)
ax.plot(x, y, color='red', linewidth=2.5, linestyle='--', label="Boundary", zorder=10)

valid_count = 0
lot_area_total = 0

# 2. 先畫土地
block_counts = {}
block_width_stats = {}  # 統計每個街廓的面寬分布
for lot_tuple in lots:
    if len(lot_tuple) == 4:
        lot, arrow_dx, arrow_dy, block_id = lot_tuple
    else:
        lot, arrow_dx, arrow_dy = lot_tuple
        block_id = 1
    x, y = get_polygon_coords(lot)
    area_ping = lot.area * 0.3025
    lot_area_total += area_ping
    centroid = lot.centroid
    
    if area_ping >= min_ping:
        valid_count += 1
        ax.fill(x, y, alpha=0.5, color='lightblue', edgecolor='black', zorder=2)
        
        lot_minx, lot_miny, lot_maxx, lot_maxy = lot.bounds
        # DXF 匯入時 arrow_dx/arrow_dy 可能為 0，改用地塊長寬比判斷方向
        if abs(arrow_dx) < 1e-9 and abs(arrow_dy) < 1e-9:
            horizontal = (lot_maxx - lot_minx) >= (lot_maxy - lot_miny)
        else:
            horizontal = abs(arrow_dx) > abs(arrow_dy)

        if horizontal:
            # faces left/right -> scale X
            xf = coverage_ratio
            yf = 1.0
            text_rot = 0
            lot_width = lot_maxy - lot_miny
        else:
            # faces up/down -> scale Y
            xf = 1.0
            yf = coverage_ratio
            text_rot = 90
            lot_width = lot_maxx - lot_minx
        
        build_poly = shapely.affinity.scale(lot, xfact=xf, yfact=yf, origin='centroid')
        build_poly = build_poly.intersection(lot)
        
        # 收集街廓面寬統計
        if block_id not in block_width_stats:
            block_width_stats[block_id] = []
        block_width_stats[block_id].append(round(lot_width, 1)) 
        
        if build_poly.geom_type == 'Polygon':
            bx, by = get_polygon_coords(build_poly)
            ax.plot(bx, by, color='blue', linewidth=0.5, alpha=0.7, zorder=3)
        elif build_poly.geom_type == 'MultiPolygon':
            for bp in build_poly.geoms:
                bx, by = get_polygon_coords(bp)
                ax.plot(bx, by, color='blue', linewidth=0.5, alpha=0.7, zorder=3)
        
        # ax.arrow(centroid.x, centroid.y, arrow_dx, arrow_dy, head_width=1.2, head_length=1.2, fc='blue', ec='blue', alpha=0.5, zorder=4)
        
        # ax.text(centroid.x, centroid.y + 1.5, f"編號: {valid_count}", ha='center', va='center', fontsize=5, fontweight='bold', zorder=5)
        build_ping = build_poly.area * 0.3025
        block_counts[block_id] = block_counts.get(block_id, 0) + 1
        # 標註地號（無背景框）
        text_label = f"{block_id_to_letter(block_id)}區-{block_counts[block_id]}\n土地:{area_ping:.1f}p\n建築:{build_ping:.1f}p"
        ax.text(centroid.x, centroid.y, text_label, ha='center', va='center', 
                fontsize=5, fontweight='bold', rotation=text_rot, color='black', zorder=25,
                bbox=dict(facecolor='white', edgecolor='none', alpha=0.78, pad=0.3))
        
        

        # 標註長寬尺寸（紅色，帶尺寸線）
        b_minx, b_miny, b_maxx, b_maxy = lot.bounds
        lot_width = b_maxx - b_minx
        lot_height = b_maxy - b_miny
        
        # 判斷長邊方向
        if lot_width > lot_height:
            # 水平長邊
            # 寬度標註（內側下方）
            dim_y = b_miny + 1.0
            # 尺寸線
            ax.plot([b_minx, b_maxx], [dim_y, dim_y], color='red', linewidth=1.0, zorder=7)
            # 端點標記
            ax.plot([b_minx, b_minx], [dim_y - 0.2, dim_y + 0.2], color='red', linewidth=1.0, zorder=7)
            ax.plot([b_maxx, b_maxx], [dim_y - 0.2, dim_y + 0.2], color='red', linewidth=1.0, zorder=7)
            # 文字
            ax.text(centroid.x, dim_y + 0.4, f"{lot_width:.1f}m", 
                   ha='center', va='top', fontsize=6, color='red', fontweight='bold', zorder=8)
            
            # 高度標註（內側左側）
            dim_x = b_minx + 1.0
            # 尺寸線
            ax.plot([dim_x, dim_x], [b_miny, b_maxy], color='red', linewidth=1.0, zorder=7)
            # 端點標記
            ax.plot([dim_x - 0.2, dim_x + 0.2], [b_miny, b_miny], color='red', linewidth=1.0, zorder=7)
            ax.plot([dim_x - 0.2, dim_x + 0.2], [b_maxy, b_maxy], color='red', linewidth=1.0, zorder=7)
            # 文字
            ax.text(dim_x - 0.4, centroid.y, f"{lot_height:.1f}m", 
                   ha='right', va='center', fontsize=6, color='red', fontweight='bold', rotation=90, zorder=8)
        else:
            # 垂直長邊
            # 高度標註（內側右側）
            dim_x = b_maxx - 1.0
            # 尺寸線
            ax.plot([dim_x, dim_x], [b_miny, b_maxy], color='red', linewidth=1.0, zorder=7)
            # 端點標記
            ax.plot([dim_x - 0.2, dim_x + 0.2], [b_miny, b_miny], color='red', linewidth=1.0, zorder=7)
            ax.plot([dim_x - 0.2, dim_x + 0.2], [b_maxy, b_maxy], color='red', linewidth=1.0, zorder=7)
            # 文字
            ax.text(dim_x + 0.4, centroid.y, f"{lot_height:.1f}m", 
                   ha='left', va='center', fontsize=6, color='red', fontweight='bold', rotation=90, zorder=8)
            
            # 寬度標註（內側下方）
            dim_y = b_miny + 1.0
            # 尺寸線
            ax.plot([b_minx, b_maxx], [dim_y, dim_y], color='red', linewidth=1.0, zorder=7)
            # 端點標記
            ax.plot([b_minx, b_minx], [dim_y - 0.2, dim_y + 0.2], color='red', linewidth=1.0, zorder=7)
            ax.plot([b_maxx, b_maxx], [dim_y - 0.2, dim_y + 0.2], color='red', linewidth=1.0, zorder=7)
            # 文字
            ax.text(centroid.x, dim_y + 0.4, f"{lot_width:.1f}m", 
                   ha='center', va='top', fontsize=6, color='red', fontweight='bold', zorder=8)

        
        # 繪製尺寸標示(面寬 - 標示在建築物短向)
        b_minx, b_miny, b_maxx, b_maxy = build_poly.bounds
        if abs(arrow_dx) > abs(arrow_dy):
            # 道路在左右側，建築物短向(面寬)在 Y 軸
            dim_x = b_minx if arrow_dx < 0 else b_maxx
            b_width = b_maxy - b_miny
        # ax.plot([dim_x, dim_x], [b_miny, b_maxy], color='darkred', linewidth=1.0, zorder=6)
        # ax.scatter([dim_x, dim_x], [b_miny, b_maxy], color='darkred', s=10, marker='|', zorder=6)
        # ax.text(dim_x, centroid.y, f"{b_width:.1f}m", ha='center', va='center', fontsize=5, color='darkred', rotation=90, bbox=dict(facecolor='white', edgecolor='none', pad=0.5, alpha=0.7), zorder=7)
        else:
            # 道路在上下側，建築物短向(面寬)在 X 軸
            dim_y = b_miny if arrow_dy < 0 else b_maxy
            b_width = b_maxx - b_minx
        # ax.plot([b_minx, b_maxx], [dim_y, dim_y], color='darkred', linewidth=1.0, zorder=6)
        # ax.scatter([b_minx, b_maxx], [dim_y, dim_y], color='darkred', s=10, marker='_', zorder=6)
        # ax.text(centroid.x, dim_y, f"{b_width:.1f}m", ha='center', va='center', fontsize=5, color='darkred', bbox=dict(facecolor='white', edgecolor='none', pad=0.5, alpha=0.7), zorder=7)


        # ax.text(centroid.x, centroid.y - 1.5, f"投影 {build_poly.area:.1f} ㎡", ha='center', va='center', fontsize=5, fontweight='bold', color='blue', zorder=5)
    else:
        ax.fill(x, y, alpha=0.3, color='lightgray', edgecolor='black', zorder=2)
        ax.text(centroid.x, centroid.y, f"畸零\n{area_ping:.1f}p", ha='center', va='center', fontsize=5, color='gray', zorder=5)

# 3. 畫道路
for r in roads:
    rx, ry = get_polygon_coords(r)
    ax.fill(rx, ry, alpha=0.8, color='dimgray', edgecolor='black', hatch='//', zorder=4)

# 3.0 路寬標示（用位置配對，不用幾何方向判斷）
if roads:
    # 收集所有設定的道路（含方向、位置、寬度）
    active_roads_info = roads_info if roads_info else []
    if not active_roads_info:
        active_roads_info = st.session_state.get('roads_info', [])
    
    v_roads_cfg = [(float(r[1]), float(r[2])) for r in active_roads_info if len(r)>=3 and str(r[0]).upper().startswith('V')]
    h_roads_cfg = [(float(r[1]), float(r[2])) for r in active_roads_info if len(r)>=3 and str(r[0]).upper().startswith('H')]
    
    for r in roads:
        rc = r.centroid
        
        # 嘗試配對到最近的設定道路（用中心座標判斷）
        best_w = 6.0
        best_dist = float('inf')
        
        # 與 V 道路配對（比較 X 座標）
        for pos, w in v_roads_cfg:
            dist = abs(rc.x - pos)
            if dist < best_dist:
                best_dist = dist
                best_w = w
        
        # 與 H 道路配對（比較 Y 座標）
        for pos, w in h_roads_cfg:
            dist = abs(rc.y - pos)
            if dist < best_dist:
                best_dist = dist
                best_w = w
        
        label_pt = r.representative_point()
        ax.text(
            label_pt.x, label_pt.y,
            f"路寬 {float(best_w):.1f}m",
            ha='center', va='center',
            fontsize=8, fontweight='bold', color='red',
            bbox=dict(facecolor='white', edgecolor='none', alpha=0.7, pad=0.2),
            zorder=20
        )

# 4. 街廓區域大標示（A/B/C/D）- 確保標示在地塊區域內，不跑到道路上
from shapely.ops import unary_union
block_lot_polys = {}
for lot_tuple in lots:
    if len(lot_tuple) == 4:
        lot, _, _, block_id = lot_tuple
    else:
        lot, _, _ = lot_tuple
        block_id = 1
    if lot.area * 0.3025 >= min_ping:
        if block_id not in block_lot_polys:
            block_lot_polys[block_id] = []
        block_lot_polys[block_id].append(lot)

# 合併道路區域（用於排除）
road_union = unary_union(roads) if roads else None

for bid, polys in block_lot_polys.items():
    if not polys:
        continue
    merged = unary_union(polys)
    
    # 確保標示點在地塊區域內（不在道路上）
    label_pt = merged.representative_point()
    
    # 如果 representative_point 落在道路上，改用地塊合併區域的質心
    if road_union and road_union.contains(label_pt):
        label_pt = merged.centroid
    
    # 如果還是在道路上，嘗試用最大地塊的中心
    if road_union and road_union.contains(label_pt):
        biggest = max(polys, key=lambda p: p.area)
        label_pt = biggest.representative_point()
    
    letter = block_id_to_letter(bid)
    # 放在區域邊緣（左上角偏移），避免被地塊文字蓋住
    bminx, bminy, bmaxx, bmaxy = merged.bounds
    lx = bminx + (bmaxx - bminx) * 0.15
    ly = bmaxy - (bmaxy - bminy) * 0.12
    ax.text(
        lx, ly, f"{letter}區",
        ha='center', va='center',
        fontsize=22, fontweight='bold', color='navy',
        alpha=0.6, zorder=30,
        bbox=dict(facecolor='white', edgecolor='none', alpha=0.5, pad=1.0)
    )



ax.set_aspect('equal')
ax.axis('off')
plt.tight_layout()

road_area = sum([r.area for r in roads]) * 0.3025 if roads else 0
total_area = base_polygon.area * 0.3025

st.markdown(f"#### 📊 基地總面積 {total_area:.1f} 坪 ｜ 道路 {road_area:.1f} 坪 ｜ 土地 {lot_area_total:.1f} 坪 ｜ 有效 {valid_count} 戶")

# 街廓面寬分析表
if block_width_stats:
    st.markdown("### 📐 街廓面寬檢討（分區分產品）")
    
    analysis_data = []
    for bid in sorted(block_width_stats.keys()):
        widths = block_width_stats[bid]
        from collections import Counter
        width_counter = Counter(widths)
        
        # 產品組合分析
        products = []
        for w, count in sorted(width_counter.items()):
            products.append(f"{w}m ({count}戶)")
        
        analysis_data.append({
            "街廓": f"{block_id_to_letter(bid)}區",
            "總戶數": len(widths),
            "產品組合": " + ".join(products),
            "主力面寬": max(width_counter, key=width_counter.get),
            "面寬範圍": f"{min(widths):.1f}m ~ {max(widths):.1f}m"
        })
    
    import pandas as pd
    df_analysis = pd.DataFrame(analysis_data)
    st.dataframe(df_analysis, width="stretch", hide_index=True)
    st.session_state['_df_analysis_csv'] = df_analysis.to_csv(index=False, encoding='utf-8-sig')
else:
    st.session_state.pop('_df_analysis_csv', None)

# 生成圖片以供下載
buf = io.BytesIO()
fig.savefig(buf, format="png", dpi=300, bbox_inches='tight')

st.sidebar.markdown("---")
st.sidebar.markdown("### 📥 圖面輸出")
st.sidebar.download_button(
    label="下載排平圖 (高畫質 PNG)",
    data=buf.getvalue(),
    file_name="layout_plan.png",
    mime="image/png"
)

col_space1, col_chart, col_space2 = st.columns([1, 8, 1])
with col_chart:
    st.pyplot(fig)








# 地號資料編輯器（在圖表顯示後）
if lots:
    st.markdown("---")
    st.markdown("### 📝 地號寬度調整")
    st.info("💡 點擊表格中的數值可以直接編輯。修改後點「重新生成」即可更新。")
    
    # 準備可編輯的地號資料
    lot_data = []
    for i, lot_tuple in enumerate(lots):
        if len(lot_tuple) == 4:
            lot, _, _, block_id = lot_tuple
        else:
            lot, _, _ = lot_tuple
            block_id = 1
        
        lot_minx, lot_miny, lot_maxx, lot_maxy = lot.bounds
        if abs(lot_maxx - lot_minx) > abs(lot_maxy - lot_miny):
            current_width = lot_maxy - lot_miny
        else:
            current_width = lot_maxx - lot_minx
        
        lot_num = len([l for l in lot_data if l["街廓"] == block_id_to_letter(block_id)]) + 1
        lot_id = f"{block_id_to_letter(block_id)}區-{lot_num}"
        
        lot_data.append({
            "地號": lot_id,
            "街廓": block_id_to_letter(block_id),
            "目前寬度(m)": round(current_width, 1),
            "期望寬度(m)": round(current_width, 1),  # 預設與目前相同
        })
    
    import pandas as pd
    df_lots = pd.DataFrame(lot_data)
    
    # 使用 data_editor 讓使用者編輯
    edited_df = st.data_editor(
        df_lots,
        column_config={
            "地號": st.column_config.TextColumn("地號", disabled=True),
            "街廓": st.column_config.TextColumn("街廓", disabled=True),
            "目前寬度(m)": st.column_config.NumberColumn("目前寬度(m)", disabled=True, format="%.1f"),
            "期望寬度(m)": st.column_config.NumberColumn("期望寬度(m)", min_value=3.0, max_value=20.0, format="%.1f"),
        },
        width="stretch",
        hide_index=True,
    )
    
    # 檢查是否有修改
    if not edited_df["期望寬度(m)"].equals(df_lots["期望寬度(m)"]):
        st.warning("⚠️ 寬度已修改，請點「重新生成」套用變更")
        
    # 保存編輯後的資料到 session_state
    st.session_state['custom_lot_widths'] = edited_df.to_dict('records')


# DXF Export
dxf_file = generate_dxf(base_polygon, lots, roads, coverage_ratio, min_ping)
with open(dxf_file, "rb") as file:
    btn = st.sidebar.download_button(
        label="下載 DXF 檔 (支援分圖層, 可轉 DWG)",
        data=file,
        file_name="land_layout.dxf",
        mime="application/dxf"
    )

# 專案打包功能
def create_project_zip():
    """打包所有專案檔案"""
    zip_buffer = io.BytesIO()
    
    with zipfile.ZipFile(zip_buffer, 'w', zipfile.ZIP_DEFLATED) as zipf:
        # 1. 儲存參數設定
        params = {
            "基地座標": list(base_coords),  # 加入基地座標
            "建築參數": {
                "基準面寬": width_req,
                "基準深度": depth_req,
                "建蔽率": coverage_ratio,
                "最小坪數": min_ping,
                "自動方向": auto_orient,
                "自動合併": auto_merge
            },
            "道路設定": roads_info,
            "街廓參數": block_params if 'block_params' in locals() else None,
            "地塊寬度調整": st.session_state.get('custom_lot_widths', None),
            "匯出時間": datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        }
        zipf.writestr("project_params.json", json.dumps(params, ensure_ascii=False, indent=2))
        
        # 2. DXF 檔案
        dxf_file = generate_dxf(base_polygon, lots, roads, coverage_ratio, min_ping)
        with open(dxf_file, 'rb') as f:
            zipf.writestr("layout_plan.dxf", f.read())
        
        # 3. PNG 圖片
        buf_img = io.BytesIO()
        fig.savefig(buf_img, format="png", dpi=300, bbox_inches='tight')
        zipf.writestr("layout_plan.png", buf_img.getvalue())
        
        # 4. 分析報表（如果有）
        if '_df_analysis_csv' in st.session_state:
            zipf.writestr("analysis_report.csv", st.session_state['_df_analysis_csv'])
    
    zip_buffer.seek(0)
    return zip_buffer.getvalue()

st.sidebar.markdown("---")
st.sidebar.markdown("### 📦 專案打包")
from datetime import datetime
project_name = st.sidebar.text_input("專案名稱", value=f"排平圖_{datetime.now().strftime('%Y%m%d')}", key="project_name_input")

if st.sidebar.button("🎁 打包下載", type="primary", width="stretch"):
    with st.spinner("正在打包..."):
        zip_data = create_project_zip()
        st.sidebar.download_button(
            label="💾 下載 ZIP",
            data=zip_data,
            file_name=f"{project_name}.zip",
            mime="application/zip",
            width="stretch",
            key="download_zip_btn"
        )
st.sidebar.caption("💡 包含：參數JSON、DXF、PNG、CSV")

# 專案載入功能
st.sidebar.markdown("---")
st.sidebar.markdown("### 📂 載入專案")
uploaded_project = st.sidebar.file_uploader("上傳專案檔案 (.dxf)", type=['dxf'], key="project_upload")

if uploaded_project is not None:
    # 檢查是否已經載入過這個檔案
    file_id = f"{uploaded_project.name}_{uploaded_project.size}"
    
    if st.session_state.get('last_loaded_file') != file_id:
        try:
            import json
            import zipfile
            import io
            
            if uploaded_project.name.endswith('.dxf'):
                # DXF 檔案：直接讀取幾何
                import ezdxf
                import tempfile
                
                # 儲存上傳的 DXF 到臨時檔案
                temp_dxf = tempfile.NamedTemporaryFile(delete=False, suffix='.dxf')
                temp_dxf.write(uploaded_project.read())
                temp_dxf.close()
                
                # 讀取 DXF
                doc = ezdxf.readfile(temp_dxf.name)
                msp = doc.modelspace()
                
                # 讀取基地邊界（BASE 圖層）
                base_points = []
                for entity in msp.query('LWPOLYLINE[layer=="SITE_BOUNDARY"]'):
                    base_points = [(p[0]/100, p[1]/100) for p in entity.get_points()]
                    break
                
                if base_points:
                    st.session_state['base_coords'] = base_points
                
                # 讀取地塊（LOT 圖層）
                lots_from_dxf = []
                for entity in msp.query('LWPOLYLINE[layer=="LOTS"]'):
                    lot_points = [(p[0]/100, p[1]/100) for p in entity.get_points()]
                    if len(lot_points) >= 3:
                        lots_from_dxf.append(Polygon(lot_points))
                
                if lots_from_dxf:
                    st.sidebar.info(f"📊 DXF 讀取: {len(lots_from_dxf)} 地塊, {len(roads_from_dxf) if 'roads_from_dxf' in dir() else '?'} 道路")
                    
                    # 讀取 TEXT 圖層的地號標籤
                    lot_labels = {}
                    # 讀取所有 TEXT 實體（不限圖層）
                    for entity in msp:
                        if entity.dxftype() != 'TEXT':
                            continue
                        if entity.dxf.layer != 'TEXT':
                            continue
                        text_content = entity.dxf.text
                        if '區-' in text_content:
                            # 解析地號，例如 "A區-1" → block_id = 1, lot_num = 1
                            parts = text_content.split('\n')[0]  # 第一行是地號
                            if '區-' in parts:
                                block_letter = parts.split('區')[0]
                                # A→1, B→2, C→3, D→4
                                block_id = ord(block_letter) - ord('A') + 1
                                # 獲取文字位置
                                text_pos = (entity.dxf.insert[0]/100, entity.dxf.insert[1]/100)
                                lot_labels[text_pos] = block_id
                    
                    # 根據地塊位置自動分配 block_id（4區分配）
                    lots_with_blocks = []
                    
                    # 有地號文字時，優先用文字位置配對地塊街廓
                    if lot_labels:
                        for lot in lots_from_dxf:
                            centroid = lot.centroid
                            min_dist = float('inf')
                            best_block_id = 1
                            for label_pos, block_id in lot_labels.items():
                                dist = ((centroid.x - label_pos[0])**2 + (centroid.y - label_pos[1])**2)**0.5
                                if dist < min_dist:
                                    min_dist = dist
                                    best_block_id = block_id
                            lots_with_blocks.append((lot, 0, 0, best_block_id))
                    else:
                        # 沒有 TEXT 標籤，根據位置自動分配
                        # 計算所有地塊的中心點
                        centroids = [(lot, lot.centroid.x, lot.centroid.y) for lot in lots_from_dxf]
                        
                        # 找出 X 和 Y 的中位數，作為分界線
                        x_coords = sorted([c[1] for c in centroids])
                        y_coords = sorted([c[2] for c in centroids])
                        x_mid = x_coords[len(x_coords)//2]
                        y_mid = y_coords[len(y_coords)//2]
                        
                        # 根據位置分配街廓 ID
                        # 左上=1(A), 右上=2(B), 左下=3(C), 右下=4(D)
                        for lot, cx, cy in centroids:
                            if cx < x_mid:
                                block_id = 1 if cy > y_mid else 3  # 左上 A, 左下 C
                            else:
                                block_id = 2 if cy > y_mid else 4  # 右上 B, 右下 D
                            lots_with_blocks.append((lot, 0, 0, block_id))
                    
                    # 調試信息
                    bid_counts = {}
                    for lt in lots_with_blocks:
                        bid = lt[3]
                        bid_counts[bid] = bid_counts.get(bid, 0) + 1
                    st.sidebar.info(f"📊 街廓分佈: {', '.join(f'{chr(64+k)}={v}' for k,v in sorted(bid_counts.items()))}")
                    
                    if lot_labels:
                        st.sidebar.success(f"✅ 讀取到 {len(lot_labels)} 個地號標籤")
                    else:
                        st.sidebar.warning("⚠️ 未讀取到地號標籤，已改用位置自動分配 A/B/C/D")
                    
                    st.session_state['imported_lots'] = lots_with_blocks
                
                # 讀取道路（ROAD 圖層）
                roads_from_dxf = []
                for entity in msp.query('LWPOLYLINE[layer=="ROAD"]'):
                    road_points = [(p[0]/100, p[1]/100) for p in entity.get_points()]
                    if len(road_points) >= 3:
                        roads_from_dxf.append(Polygon(road_points))
                
                if roads_from_dxf:
                    st.session_state['imported_roads'] = roads_from_dxf
                
                # 保留臨時檔案供調試
                import os
                import shutil
                debug_dxf = '/tmp/last_imported.dxf'
                shutil.copy2(temp_dxf.name, debug_dxf)
                os.unlink(temp_dxf.name)
                
                # 標記為已載入 DXF
                st.session_state['loaded_from_dxf'] = True

                # DXF 匯入後：反推參數並同步回左側欄位
                if 'imported_roads' in st.session_state and 'base_coords' in st.session_state:
                    roads = st.session_state['imported_roads']
                    base_polygon = Polygon(st.session_state['base_coords'])
                    
                    # 反推道路參數（按街廓分組，找街廓之間的間隙）
                    inferred_roads_info = []
                    
                    if 'imported_lots' in st.session_state:
                        imp_lots = st.session_state['imported_lots']
                        
                        # 按 block_id 分組，計算每組的整體邊界
                        block_bounds = {}
                        for lt in imp_lots:
                            bid = lt[3] if len(lt) == 4 else 1
                            b = lt[0].bounds
                            if bid not in block_bounds:
                                block_bounds[bid] = [b[0], b[1], b[2], b[3]]
                            else:
                                bb = block_bounds[bid]
                                bb[0] = min(bb[0], b[0])
                                bb[1] = min(bb[1], b[1])
                                bb[2] = max(bb[2], b[2])
                                bb[3] = max(bb[3], b[3])
                        
                        bids = sorted(block_bounds.keys())
                        
                        # 找 X 方向間隙（直向道路）
                        v_gaps = []
                        for i in range(len(bids)):
                            for j in range(i+1, len(bids)):
                                bb1 = block_bounds[bids[i]]
                                bb2 = block_bounds[bids[j]]
                                # 兩塊在 Y 方向有重疊，X 方向有間隙
                                y_overlap = min(bb1[3], bb2[3]) - max(bb1[1], bb2[1])
                                if y_overlap > 1.0:
                                    x_gap = max(bb2[0] - bb1[2], bb1[0] - bb2[2])
                                    if 0.5 < x_gap < 20.0:
                                        pos = (min(bb1[2], bb2[2]) + max(bb1[0], bb2[0])) / 2
                                        if bb1[2] < bb2[0]:
                                            pos = (bb1[2] + bb2[0]) / 2
                                        elif bb2[2] < bb1[0]:
                                            pos = (bb2[2] + bb1[0]) / 2
                                        v_gaps.append(('V', round(pos, 1), round(x_gap, 1)))
                        
                        # 找 Y 方向間隙（橫向道路）
                        h_gaps = []
                        for i in range(len(bids)):
                            for j in range(i+1, len(bids)):
                                bb1 = block_bounds[bids[i]]
                                bb2 = block_bounds[bids[j]]
                                # 兩塊在 X 方向有重疊，Y 方向有間隙
                                x_overlap = min(bb1[2], bb2[2]) - max(bb1[0], bb2[0])
                                if x_overlap > 1.0:
                                    y_gap = max(bb2[1] - bb1[3], bb1[1] - bb2[3])
                                    if 0.5 < y_gap < 20.0:
                                        if bb1[3] < bb2[1]:
                                            pos = (bb1[3] + bb2[1]) / 2
                                        elif bb2[3] < bb1[1]:
                                            pos = (bb2[3] + bb1[1]) / 2
                                        else:
                                            continue
                                        h_gaps.append(('H', round(pos, 1), round(y_gap, 1)))
                        
                        # 去重
                        for gaps in [v_gaps, h_gaps]:
                            deduped = []
                            for g in gaps:
                                is_dup = False
                                for d in deduped:
                                    if abs(g[1] - d[1]) < 5.0:
                                        is_dup = True
                                        break
                                if not is_dup:
                                    deduped.append(g)
                            inferred_roads_info.extend(deduped)
                    
                    # 路寬四捨五入到 0.5 倍數，最小 1.5m
                    rounded_roads = []
                    for ri in inferred_roads_info:
                        w = ri[2]
                        w = max(1.5, round(w * 2) / 2)  # 四捨五入到 0.5
                        rounded_roads.append((ri[0], ri[1], w))
                    inferred_roads_info = rounded_roads
                    
                    # 如果沒推出來，用預設值
                    if not inferred_roads_info:
                        inferred_roads_info = [('V', 50.0, 6.0), ('H', 50.0, 6.0)]
                    
                    # 回填 roads_info（供路寬標註使用）
                    if inferred_roads_info:
                        st.session_state['roads_info'] = inferred_roads_info
                        st.session_state['road_count'] = len(inferred_roads_info)
                        
                        # 標記需要清除舊 slider keys（下次 rerun 開頭執行）
                        st.session_state['_dxf_clear_widget_keys'] = True
                    
                    # 反推基地尺寸
                    bminx, bminy, bmaxx, bmaxy = base_polygon.bounds
                    st.session_state['base_width'] = round(bmaxx - bminx, 1)
                    st.session_state['base_height'] = round(bmaxy - bminy, 1)
                    

                    
                    # 反推最小坪數及面寬/深度
                    if 'imported_lots' in st.session_state:
                        lots = st.session_state['imported_lots']
                        valid_areas = []
                        lot_widths = []
                        lot_depths = []
                        for lot_tuple in lots:
                            poly = lot_tuple[0]
                            area_ping = poly.area * 0.3025
                            if area_ping >= 10:
                                valid_areas.append(area_ping)
                                lminx, lminy, lmaxx, lmaxy = poly.bounds
                                w = lmaxx - lminx
                                h = lmaxy - lminy
                                lot_widths.append(min(w, h))
                                lot_depths.append(max(w, h))
                        if valid_areas:
                            median_area = sorted(valid_areas)[len(valid_areas)//2]
                            st.session_state['min_ping'] = max(15, round(median_area * 0.6, 0))
                            # 反推面寬/深度（取中位數）
                            if lot_widths:
                                st.session_state['width_req'] = round(sorted(lot_widths)[len(lot_widths)//2], 1)
                            if lot_depths:
                                st.session_state['depth_req'] = round(sorted(lot_depths)[len(lot_depths)//2], 1)
                        else:
                            st.session_state['min_ping'] = 20
                
                st.session_state['last_loaded_file'] = file_id
                
                # 保存反推參數快照（用於偵測左側是否有改動）
                st.session_state['dxf_snapshot'] = {
                    'roads_info': list(st.session_state.get('roads_info', [])),
                    'width_req': st.session_state.get('width_req'),
                    'depth_req': st.session_state.get('depth_req'),
                    'min_ping': st.session_state.get('min_ping'),
                }
                
                st.sidebar.success(f"✅ 已載入 DXF 幾何：{uploaded_project.name}")
                st.sidebar.info("💡 左側參數已同步，調整參數後會自動重新生成")
                st.rerun()
            else:
                st.sidebar.error('❌ 目前僅支援 DXF 匯入')
                st.stop()
                # ZIP 或 JSON
                if uploaded_project.name.endswith('.zip'):
                    # ZIP 檔案：解壓並讀取
                    zip_buffer = io.BytesIO(uploaded_project.read())
                    with zipfile.ZipFile(zip_buffer, 'r') as zipf:
                        # 讀取 JSON
                        json_data = zipf.read('project_params.json')
                        project_data = json.loads(json_data.decode('utf-8'))
                        
                        # 儲存 PNG 圖片到 session_state（作為參考）
                        if 'layout_plan.png' in zipf.namelist():
                            st.session_state['reference_image'] = zipf.read('layout_plan.png')
                else:
                    # JSON 檔案：直接讀取
                    project_data = json.load(uploaded_project)
                
                # 恢復參數
                if '基地座標' in project_data:
                    st.session_state['base_coords'] = [tuple(coord) for coord in project_data['基地座標']]
                
                if '建築參數' in project_data:
                    params = project_data['建築參數']
                    st.session_state['width_req'] = params.get('基準面寬', 5.0)
                    st.session_state['depth_req'] = params.get('基準深度', 20.0)
                    st.session_state['coverage_ratio'] = params.get('建蔽率', 0.6)
                    st.session_state['min_ping'] = params.get('最小坪數', 20.0)
                    st.session_state['auto_orient'] = params.get('自動方向', True)
                    st.session_state['auto_merge'] = params.get('自動合併', False)
                
                if '道路設定' in project_data:
                    st.session_state['roads_info'] = project_data['道路設定']
                
                if '街廓參數' in project_data and project_data['街廓參數']:
                    st.session_state['block_params'] = project_data['街廓參數']
                
                # 恢復地塊寬度調整
                if '地塊寬度調整' in project_data and project_data['地塊寬度調整']:
                    st.session_state['custom_lot_widths'] = project_data['地塊寬度調整']
                
                # 記錄已載入的檔案
                st.session_state['last_loaded_file'] = file_id
                st.session_state['project_loaded'] = True
                
                st.sidebar.success(f"✅ 已載入專案：{uploaded_project.name}")
                
                # 如果有參考圖片，顯示提示
                if 'reference_image' in st.session_state:
                    st.sidebar.info("💡 參考圖片已載入")
                
                st.rerun()
        except Exception as e:
            st.sidebar.error(f"❌ 載入失敗：{e}")
    else:
        st.sidebar.info(f"📂 專案已載入：{uploaded_project.name}")

st.sidebar.caption("💡 僅支援上傳 DXF 檔案")

# 清除 DXF 匯入
if st.session_state.get('loaded_from_dxf', False):
    if st.sidebar.button("🔄 切換回參數生成模式", width="stretch"):
        st.session_state['loaded_from_dxf'] = False
        st.session_state.pop('imported_lots', None)
        st.session_state.pop('imported_roads', None)
        st.rerun()
