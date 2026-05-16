<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class PolicyStatusColumnMaster extends BaseModel
{
    use HasFactory;
    protected $table = 'policystatus_column_master';
    protected $fillable = [
        'column_name',
        'alias',
        'is_default',
        'is_visible',
        'lob',
        'stage',
        'order_by'
    ];
    protected $logAttributes = ['column_name','is_visible'];
    
    
    public function excelKeys()
    {
        return $this->hasMany(ExcelKeyMaster::class, 'policystatus_column_master_id', 'id');
    }
}
