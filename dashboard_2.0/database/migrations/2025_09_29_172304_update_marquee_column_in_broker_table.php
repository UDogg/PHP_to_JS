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
        Schema::table('broker', function (Blueprint $table) {
            $table->dropColumn('marquee');
        });

        Schema::table('broker', function (Blueprint $table) {
            $table->char('marquee', 1)->default('N');
        });
    }

    public function down(): void
    {
        Schema::table('broker', function (Blueprint $table) {
            $table->dropColumn('marquee');
        });

        Schema::table('broker', function (Blueprint $table) {
            $table->string('marquee', 255)->nullable();
        });
    }
};
