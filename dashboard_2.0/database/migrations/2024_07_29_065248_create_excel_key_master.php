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
        Schema::create('excel_key_master', function (Blueprint $table) {
            $table->id('excel_key_master_id');
            $table->string('policystatus_column_master_id');
            $table->string('excel_column_name');
            $table->string('sequence')->nullable();
            $table->string('is_visible');
            $table->timestamps();
            $table->softDeletes();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('excel_key_master');
    }
};
