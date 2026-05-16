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
        Schema::table('lob_master', function (Blueprint $table) {
            $table->enum('redirect_insame_tab',['Y','N'])->default('Y');
            $table->string('frontend_url')->nullable();
            $table->string('lob_icon')->nullable();
            $table->timestamp('deleted_at')->nullable();

        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('lob_master', function (Blueprint $table) {
            //
        });
    }
};
