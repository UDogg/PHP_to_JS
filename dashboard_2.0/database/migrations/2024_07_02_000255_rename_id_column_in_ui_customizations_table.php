<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        Schema::table('ui_customizations', function (Blueprint $table) {
            if(Schema::hasColumn('ui_customizations','ui_customization_id'))
            {
                return true;
            }
            if(!Schema::hasColumn('ui_customizations','placeholder_id'))
            {
                $table->renameColumn('placeholder_id','ui_customization_id');
            }
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('ui_customizations', function (Blueprint $table) {

        });
    }
};
