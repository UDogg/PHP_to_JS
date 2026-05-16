<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class ExcelKeyMaster extends BaseModel
{
    use HasFactory;
    protected $table = 'excel_key_master';
    protected $primaryKey = 'excel_key_master_id';
    protected $fillable = ['policystatus_column_master_id','excel_column_name','sequence','is_visible','lob_id','sample_data'];
    protected $logAttributes = ['policystatus_column_master_id','excel_column_name','sequence','is_visible','lob_id'];

    public function policyStatusColumns()
    {
        return $this->belongsTo(PolicyStatusColumnMaster::class, 'policystatus_column_master_id', 'id');
    }
}
