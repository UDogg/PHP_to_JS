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
        if (Schema::hasTable('posp_ic_mappings')){
                Schema::table('posp_ic_mappings', function (Blueprint $table) {
                $table->renameColumn('posp_id', 'user_id');
            });
        }

    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('posp_ic_mappings', function (Blueprint $table) {
            //
        });
    }
};
