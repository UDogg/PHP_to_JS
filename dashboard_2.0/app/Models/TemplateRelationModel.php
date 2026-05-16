<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class TemplateRelationModel extends BaseModel
{
    use HasFactory;
    protected $table = 'template_relation';
    protected $primaryKey = 'template_relation_id';
    protected $guarded = [];
    protected $fillable = [
      'template_id',
      'user_type_id',
      'role_id',
    ];
    protected $logAttributes = [
      'template_id',
      'user_type_id',
      'role_id',
    ];
}
